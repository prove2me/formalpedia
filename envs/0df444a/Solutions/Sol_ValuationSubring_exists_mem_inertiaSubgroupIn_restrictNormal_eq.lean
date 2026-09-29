-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_restrictNormal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c7b29861-e1e9-504b-baf2-a211f4d7161b

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroup_map_subtype_iff
import Theorems.Thm_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq
import Theorems.Thm_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq

set_option autoImplicit false

open scoped Pointwise

namespace S17IOI

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem {F : Type*} [Field F] (V : ValuationSubring F) (x : F) :
    x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · simp [hx]
  · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hx), not_le]
    simp [hx]

theorem mem_nonunits_comap_iff (A : ValuationSubring L) (M : IntermediateField K L) (z : M) :
    z ∈ (A.comap (algebraMap M L)).nonunits ↔ algebraMap M L z ∈ A.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem, map_eq_zero_iff _ (algebraMap M L).injective,
    ValuationSubring.mem_comap, map_inv₀]

end S17IOI

open S17IOI in

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (M : IntermediateField K L) [Normal K M]
    (A : ValuationSubring L) (τ : M ≃ₐ[K] M)
    (hτ : τ ∈ (A.comap (algebraMap M L)).inertiaSubgroupIn K) :
    ∃ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K ∧ σ.restrictNormal M = τ := by

  obtain ⟨hτB, hτres⟩ := (ValuationSubring.mem_inertiaSubgroup_map_subtype_iff (A.comap (algebraMap M L)) τ).mp hτ
  have hτB' : τ • (A.comap (algebraMap M L)) = A.comap (algebraMap M L) := by
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · intro h
      have := (hτB (τ⁻¹ y)).mpr h
      rwa [show τ (τ⁻¹ y) = y from by change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    · intro h
      apply (hτB (τ⁻¹ y)).mp
      rwa [show τ (τ⁻¹ y) = y from by change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl]

  obtain ⟨σ₀, hσ₀D, hσ₀τ⟩ := ValuationSubring.exists_mem_decompositionSubgroup_restrictNormal_eq M A τ hτB'
  have hres₀ : ∀ m : M, σ₀ (algebraMap M L m) = algebraMap M L (τ m) := fun m => by
    rw [← hσ₀τ, AlgEquiv.restrictNormal_commutes]
  have hσ₀A : ∀ x : L, σ₀ x ∈ A ↔ x ∈ A := by
    intro x
    have h1 : x ∈ σ₀⁻¹ • A ↔ σ₀ x ∈ A := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
    rw [← h1]
    have : σ₀⁻¹ • A = A := by
      have h := hσ₀D
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h
      rw [inv_smul_eq_iff]; exact h.symm
    rw [this]

  let d₀ : A.decompositionSubgroup K := ⟨σ₀, hσ₀D⟩
  let φ : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A :=
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) d₀
  have hφ : ∀ a : A, φ (IsLocalRing.residue A a) = IsLocalRing.residue A (d₀ • a) := by
    intro a
    show d₀ • IsLocalRing.residue A a = _
    rw [IsLocalRing.ResidueField.residue_smul]
  have hd₀a : ∀ a : A, ((d₀ • a : A) : L) = σ₀ (a : L) := fun a => rfl

  haveI : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have hφM : ∀ (m : M) (hm : algebraMap M L m ∈ A),
      φ (IsLocalRing.residue A ⟨algebraMap M L m, hm⟩) = IsLocalRing.residue A ⟨algebraMap M L m, hm⟩ := by
    intro m hm
    have hmB : m ∈ A.comap (algebraMap M L) := hm
    have hmove := hτres m hmB
    rw [mem_nonunits_comap_iff, map_sub, ← hres₀] at hmove

    have hσm : σ₀ (algebraMap M L m) ∈ A := (hσ₀A _).mpr hm
    have hsubmax : (⟨σ₀ (algebraMap M L m), hσm⟩ - ⟨algebraMap M L m, hm⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      exact hmove
    rw [hφ, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : (d₀ • (⟨algebraMap M L m, hm⟩ : A)) = ⟨σ₀ (algebraMap M L m), hσm⟩ := Subtype.ext rfl
    rw [this]

    have := Ideal.neg_mem_iff (IsLocalRing.maximalIdeal A) |>.mpr hsubmax
    rwa [neg_sub] at this

  obtain ⟨g, hgD, hg⟩ := ValuationSubring.exists_mem_decompositionSubgroup_forall_residue_smul_eq (K := M) A φ hφM
  have hgA : ∀ x : L, g x ∈ A ↔ x ∈ A := by
    intro x
    have h1 : x ∈ g⁻¹ • A ↔ g x ∈ A := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
    rw [← h1]
    have : g⁻¹ • A = A := by
      have h := hgD
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h
      rw [inv_smul_eq_iff]; exact h.symm
    rw [this]

  let g' : L ≃ₐ[K] L := g.restrictScalars K
  have hg'apply : ∀ x, g' x = g x := fun _ => rfl
  refine ⟨σ₀ * g'⁻¹, ?_, ?_⟩
  ·
    rw [ValuationSubring.inertiaSubgroupIn, ValuationSubring.mem_inertiaSubgroup_map_subtype_iff]
    have hg'inv : ∀ x, g'⁻¹ x = g⁻¹ x := fun _ => rfl
    constructor
    · intro x
      rw [AlgEquiv.mul_apply, hσ₀A, hg'inv]
      have := hgA (g⁻¹ x)
      rw [show g (g⁻¹ x) = x from by change (g * g⁻¹) x = x; rw [mul_inv_cancel]; rfl] at this
      exact this.symm
    · intro a ha
      rw [AlgEquiv.mul_apply, hg'inv]
      set b := g⁻¹ a with hb
      have hbA : b ∈ A := by
        rw [← hgA, hb, show g (g⁻¹ a) = a from by change (g * g⁻¹) a = a; rw [mul_inv_cancel]; rfl]
        exact ha
      have hab : a = g b := by rw [hb]; change a = (g * g⁻¹) a; rw [mul_inv_cancel]; rfl
      have hσbA : σ₀ b ∈ A := (hσ₀A b).mpr hbA

      have e1 : IsLocalRing.residue A ⟨σ₀ b, hσbA⟩ = φ (IsLocalRing.residue A ⟨b, hbA⟩) := by
        rw [hφ]; rfl
      have e2 : IsLocalRing.residue A ⟨a, ha⟩ = φ (IsLocalRing.residue A ⟨b, hbA⟩) := by
        rw [← hg ⟨b, hbA⟩]
        congr 1
        exact Subtype.ext hab
      have hcoe : ((⟨σ₀ b, hσbA⟩ - ⟨a, ha⟩ : A) : L) = σ₀ b - a := rfl
      rw [← hcoe, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_sub, e1, e2, sub_self]
  ·
    apply AlgEquiv.ext
    intro m
    apply (algebraMap M L).injective
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.mul_apply, ← hres₀]
    congr 1
    show g⁻¹ (algebraMap M L m) = algebraMap M L m
    exact (g⁻¹).commutes m

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq (solution)
