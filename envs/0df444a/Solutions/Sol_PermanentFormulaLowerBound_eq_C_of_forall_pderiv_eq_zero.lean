-- Prove2me | solution 1 for PermanentFormulaLowerBound.eq_C_of_forall_pderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/099315e4-3c68-40d9-81fe-f605c5dd224a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [Field F] [CharZero F]
    (p : MvPolynomial ι F)
    (hp : ∀ i : ι, MvPolynomial.pderiv i p = 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  classical
  apply MvPolynomial.ext _ _
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hnone
      apply hm
      ext i
      simp only [Finsupp.zero_apply]
      exact Classical.byContradiction (fun hi => hnone ⟨i, hi⟩)
    let m' : ι →₀ ℕ := m - Finsupp.single i 1
    have hcancel : m' + Finsupp.single i 1 = m := by
      exact Finsupp.sub_add_single_one_cancel hi
    have hder := congrArg (MvPolynomial.coeff m') (hp i)
    rw [MvPolynomial.coeff_pderiv, hcancel, MvPolynomial.coeff_zero] at hder
    have hcast : (↑(m' i) + 1 : F) ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    have hcoeff : MvPolynomial.coeff m p = 0 :=
      (mul_eq_zero.mp hder).resolve_right hcast
    simpa [Ne.symm hm] using hcoeff
end PermanentFormulaLowerBound
