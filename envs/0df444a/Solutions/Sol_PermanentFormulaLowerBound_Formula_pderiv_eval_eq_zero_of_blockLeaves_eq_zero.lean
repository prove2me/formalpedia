-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.pderiv_eval_eq_zero_of_blockLeaves_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/f4b17fa5-a685-4aab-b791-547f9daf7a6f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {ι F : Type*} [CommRing F] [DecidableEq ι]
    (f : Formula ι F) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    blockLeaves s f = 0 → MvPolynomial.pderiv i (eval f) = 0 := by
  classical
  induction f with
  | var j =>
      intro hleaves
      have hj : j ∉ s := by
        intro hjs
        simp [blockLeaves, hjs] at hleaves
      have hne : j ≠ i := by
        intro heq
        exact hj (heq.symm ▸ hi)
      exact MvPolynomial.pderiv_X_of_ne hne
  | const c =>
      intro _
      exact MvPolynomial.pderiv_C
  | add f g hf hg =>
      intro hleaves
      have hleft : blockLeaves s f = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      have hright : blockLeaves s g = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      simp [eval, hf hleft, hg hright]
  | sub f g hf hg =>
      intro hleaves
      have hleft : blockLeaves s f = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      have hright : blockLeaves s g = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      simp [eval, hf hleft, hg hright]
  | mul f g hf hg =>
      intro hleaves
      have hleft : blockLeaves s f = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      have hright : blockLeaves s g = 0 := by
        simp only [blockLeaves] at hleaves
        omega
      simp [eval, hf hleft, hg hright]
end PermanentFormulaLowerBound.Formula
