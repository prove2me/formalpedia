-- Prove2me | solution 1 for ValuationSubring.exists_inertiaSubgroup_restrictNormal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d9ba24b2-3247-5d90-a2da-bf6603452bc1

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise

local notation "Qb" => AlgebraicClosure ℚ

namespace InertiaRestrict

theorem inertia_restrictNormal (L : IntermediateField ℚ Qb) [FiniteDimensional ℚ L]
    [Normal ℚ L] (A : ValuationSubring Qb) (σ : A.inertiaSubgroup ℚ) :
    ∃ τ : (A.comap (algebraMap L Qb)).inertiaSubgroup ℚ,
      ((τ : (A.comap (algebraMap L Qb)).decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L)
        = AlgEquiv.restrictNormalHom L
            ((σ : A.decompositionSubgroup ℚ) : Qb ≃ₐ[ℚ] Qb) := by
  obtain ⟨⟨σ₀, hσdec⟩, hσin⟩ := σ
  set S : ValuationSubring L := A.comap (algebraMap L Qb) with hS
  set τ₀ : L ≃ₐ[ℚ] L := AlgEquiv.restrictNormalHom L σ₀ with hτ₀

  have hσA : σ₀ • A = A := hσdec

  have hcomm : ∀ x : L, algebraMap L Qb (τ₀ x) = σ₀ (algebraMap L Qb x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ₀ L x
  have hcomm_inv : ∀ x : L, algebraMap L Qb (τ₀⁻¹ x) = σ₀⁻¹ (algebraMap L Qb x) := by
    intro x
    have : τ₀⁻¹ = AlgEquiv.restrictNormalHom L σ₀⁻¹ := by
      rw [hτ₀, ← map_inv]
    rw [this]
    exact AlgEquiv.restrictNormal_commutes σ₀⁻¹ L x

  have hτdec : τ₀ ∈ S.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap]
    have hx : algebraMap L Qb (τ₀⁻¹ • x) = σ₀⁻¹ • (algebraMap L Qb x) := hcomm_inv x
    rw [hx, ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hσA]

  set ι : S →+* A :=
    RingHom.codRestrict ((algebraMap L Qb).comp S.subtype) A.toSubring
      (fun x => ValuationSubring.mem_comap.mp x.2) with hι

  have hσres : ∀ b : A, IsLocalRing.residue A ((⟨σ₀, hσdec⟩ : A.decompositionSubgroup ℚ) • b)
      = IsLocalRing.residue A b := by
    intro b
    have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ)
        (IsLocalRing.ResidueField A) ⟨σ₀, hσdec⟩ = 1 := hσin
    have h2 := RingEquiv.ext_iff.mp h1 (IsLocalRing.residue A b)
    rw [IsLocalRing.ResidueField.residue_smul]
    exact h2

  have hτin : (⟨τ₀, hτdec⟩ : S.decompositionSubgroup ℚ) ∈ S.inertiaSubgroup ℚ := by
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    show (⟨τ₀, hτdec⟩ : S.decompositionSubgroup ℚ) • IsLocalRing.residue S y
      = IsLocalRing.residue S y
    rw [← IsLocalRing.ResidueField.residue_smul]

    have key : (⟨τ₀, hτdec⟩ : S.decompositionSubgroup ℚ) • y - y ∈ IsLocalRing.maximalIdeal S := by
      have himg : ι ((⟨τ₀, hτdec⟩ : S.decompositionSubgroup ℚ) • y - y)
          ∈ IsLocalRing.maximalIdeal A := by
        have hιsmul : ι ((⟨τ₀, hτdec⟩ : S.decompositionSubgroup ℚ) • y)
            = (⟨σ₀, hσdec⟩ : A.decompositionSubgroup ℚ) • ι y := by
          apply Subtype.ext
          exact hcomm y.val
        rw [map_sub, hιsmul]
        have := hσres (ι y)
        exact Ideal.Quotient.eq.mp this
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at himg ⊢
      exact fun h => himg (h.map ι)
    exact Ideal.Quotient.eq.mpr key
  exact ⟨⟨⟨τ₀, hτdec⟩, hτin⟩, rfl⟩

end InertiaRestrict

theorem solution
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [Normal ℚ L]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : A.inertiaSubgroup ℚ) :
    ∃ τ : (A.comap (algebraMap L (AlgebraicClosure ℚ))).inertiaSubgroup ℚ,
      ((τ : (A.comap (algebraMap L (AlgebraicClosure ℚ))).decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L)
        = AlgEquiv.restrictNormalHom L
            ((σ : A.decompositionSubgroup ℚ) : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :=
  InertiaRestrict.inertia_restrictNormal L A σ

end S_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq
end P2MW
export P2MW.S_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq (solution)
