-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_coordinateSubset_quotient_ringKrullDim_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/20465388-5214-4645-9ac1-6e0bb4e73cf1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ringKrullDim_le_of_isIntegral
import Theorems.Thm_PermanentRollout_homogeneousMap_isIntegral

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (coordinates : Finset ι) :
    ringKrullDim
      (MvPolynomial ι ℂ ⧸
        Ideal.span (F '' (coordinates : Set ι))) ≤
      ((Fintype.card ι - coordinates.card : ℕ) : WithBot ℕ∞) := by
  classical
  let R := MvPolynomial ι ℂ
  let T := homogeneousMapSubalgebra F
  let J : Ideal R := Ideal.span (F '' (coordinates : Set ι))
  let P : Ideal T := J.comap (algebraMap T R)
  let E : MvPolynomial ι ℂ ≃ₐ[ℂ] T :=
    homogeneousMapCoordinateAlgEquiv F e he hF hzero
  letI : Algebra.IsIntegral T R :=
    homogeneousMap_isIntegral F e he hF hzero
  letI : Algebra.IsIntegral (T ⧸ P) (R ⧸ J) :=
    Algebra.IsIntegral.quotient
  let remaining := {i : ι // i ∉ coordinates}
  let psi : MvPolynomial ι ℂ →ₐ[ℂ] T ⧸ P :=
    (Ideal.Quotient.mkₐ ℂ P).comp E.toAlgHom
  let phi : MvPolynomial remaining ℂ →ₐ[ℂ] T ⧸ P :=
    MvPolynomial.aeval fun i : remaining =>
      psi (MvPolynomial.X i.val)
  have hpsi_coordinate (i : ι) (hi : i ∈ coordinates) :
      psi (MvPolynomial.X i) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (E (MvPolynomial.X i) : R) ∈ J
    change MvPolynomial.aeval F (MvPolynomial.X i) ∈ J
    simp only [MvPolynomial.aeval_X]
    exact Ideal.subset_span ⟨i, hi, rfl⟩
  have hsurj : Function.Surjective phi := by
    have hpsisurj : Function.Surjective psi :=
      (Ideal.Quotient.mkₐ_surjective ℂ P).comp E.surjective
    have hrange : psi.range ≤ phi.range := by
      rintro x ⟨f, rfl⟩
      induction f using MvPolynomial.induction_on with
      | C c =>
          change psi (MvPolynomial.C c) ∈ phi.range
          simp
      | add f g hf hg =>
          rw [map_add]
          exact phi.range.add_mem hf hg
      | mul_X f i hf =>
          rw [map_mul]
          apply phi.range.mul_mem hf
          by_cases hi : i ∈ coordinates
          · change psi (MvPolynomial.X i) ∈ phi.range
            rw [hpsi_coordinate i hi]
            exact phi.range.zero_mem
          · change psi (MvPolynomial.X i) ∈ phi.range
            exact ⟨MvPolynomial.X (⟨i, hi⟩ : remaining), by
              simp [phi]⟩
    intro x
    obtain ⟨f, hf⟩ := hpsisurj x
    have hx : x ∈ psi.range := ⟨f, hf⟩
    exact hrange hx
  change ringKrullDim (R ⧸ J) ≤ _
  calc
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (T ⧸ P) :=
      ringKrullDim_le_of_isIntegral (R := T ⧸ P) (S := R ⧸ J)
    _ ≤ ringKrullDim (MvPolynomial remaining ℂ) :=
      ringKrullDim_le_of_surjective phi.toRingHom hsurj
    _ = ((Fintype.card ι - coordinates.card : ℕ) : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
      simp only [zero_add]
      congr 1
      simp [remaining]
end PermanentRollout
