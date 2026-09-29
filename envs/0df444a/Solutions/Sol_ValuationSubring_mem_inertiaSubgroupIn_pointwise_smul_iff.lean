-- Prove2me | solution 1 for ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c1fa7ffc-44fc-5d84-8daa-6ad741d1e16e

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff

set_option autoImplicit false

open scoped Pointwise

namespace WCOTInertiaConj

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

theorem mem_nonunits_iff_mem_and (B : ValuationSubring L) (x : L) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro hx
    refine ⟨(B.valuation_le_one_iff x).mp hx.le, ?_⟩
    rcases eq_or_ne x 0 with h0 | h0
    · exact Or.inl h0
    · right
      rw [← B.valuation_le_one_iff, not_le]
      exact (B.valuation.val_lt_one_iff h0).mp hx
  · rintro ⟨hxB, h0 | hinv⟩
    · rw [h0, map_zero]; exact zero_lt_one
    · have hx0 : x ≠ 0 := by rintro rfl; exact hinv (by rw [inv_zero]; exact B.zero_mem)
      rw [← B.valuation_le_one_iff, not_le] at hinv
      exact (B.valuation.val_lt_one_iff hx0).mpr hinv

theorem mem_nonunits_pointwise_smul_iff (g : L ≃ₐ[K] L) (B : ValuationSubring L) (x : L) :
    x ∈ (g • B).nonunits ↔ g⁻¹ x ∈ B.nonunits := by
  rw [mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ g⁻¹.injective]

theorem valuation_lt_one_pointwise_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    (g • A).valuation x < 1 ↔ A.valuation (g⁻¹ x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff]
  exact mem_nonunits_pointwise_smul_iff g A x

theorem mem_inertia_map_pointwise_smul_iff (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ ((g • A).inertiaSubgroup K).map ((g • A).decompositionSubgroup K).subtype ↔
      g⁻¹ * σ * g ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype := by
  rw [mem_inertia_map_iff, mem_inertia_map_iff]
  have hD : σ ∈ (g • A).decompositionSubgroup K ↔ g⁻¹ * σ * g ∈ A.decompositionSubgroup K := by
    simp only [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  have hconj : ∀ b : L, (g⁻¹ * σ * g) b - b = g⁻¹ (σ (g b) - g b) := fun b => by
    rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g⁻¹ g b, inv_mul_cancel,
      AlgEquiv.one_apply]
  refine and_congr hD ⟨fun h b => ?_, fun h a => ?_⟩
  · have hb : g (b : L) ∈ g • A := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← AlgEquiv.mul_apply,
        inv_mul_cancel, AlgEquiv.one_apply]
      exact b.2
    have h1 := h ⟨g b, hb⟩
    rw [valuation_lt_one_pointwise_smul_iff] at h1
    rw [hconj]
    exact h1
  · have ha : g⁻¹ (a : L) ∈ A := by
      have := a.2
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def] at this
      exact this
    have h1 := h ⟨g⁻¹ a, ha⟩
    rw [valuation_lt_one_pointwise_smul_iff]
    have e : (g⁻¹ * σ * g) (g⁻¹ (a : L)) - g⁻¹ (a : L) = g⁻¹ (σ a - a) := by
      rw [hconj, ← AlgEquiv.mul_apply g g⁻¹ (a : L), mul_inv_cancel, AlgEquiv.one_apply]
    rw [← e]
    exact h1

theorem mem_inertia_pointwise_smul_aux (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).inertiaSubgroupIn K ↔ g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K :=
  mem_inertia_map_pointwise_smul_iff g σ A

theorem forall_inertia_eq_zero_of_conj {M : Type} [Zero M] {q : ℕ} (P : ValuationSubring L)
    (hconj : ∀ P' : ValuationSubring L, P'.LiesOverPrime q → ∃ g : L ≃ₐ[K] L, g • P = P')
    (Λ : (L ≃ₐ[K] L) → M)
    (hΛconj : ∀ (g τ : L ≃ₐ[K] L), τ ∈ P.inertiaSubgroupIn K → Λ τ = 0 → Λ (g * τ * g⁻¹) = 0)
    (h0 : ∀ τ ∈ P.inertiaSubgroupIn K, Λ τ = 0) :
    ∀ P' : ValuationSubring L, P'.LiesOverPrime q → ∀ τ ∈ P'.inertiaSubgroupIn K, Λ τ = 0 := by
  intro P' hP' τ hτ
  obtain ⟨g, rfl⟩ := hconj P' hP'
  have hτ' : g⁻¹ * τ * g ∈ P.inertiaSubgroupIn K := (mem_inertia_pointwise_smul_aux g τ P).mp hτ
  have h := hΛconj g _ hτ' (h0 _ hτ')
  have e : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
  rw [e] at h
  exact h

end WCOTInertiaConj

open scoped Pointwise

theorem solution
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (g σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    σ ∈ (g • A).inertiaSubgroupIn K ↔ g⁻¹ * σ * g ∈ A.inertiaSubgroupIn K := by
  exact WCOTInertiaConj.mem_inertia_pointwise_smul_aux g σ A

end S_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
end P2MW
export P2MW.S_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff (solution)
