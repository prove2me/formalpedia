-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_pderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/7886ff16-c8f5-410f-bde7-eaa8f0104ef2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_pderiv_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) (y : Y) :
    MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) ≠ 0 := by
  have hrename := MvPolynomial.pderiv_rename
    (matchingVariableEquiv d).symm.injective (d y)
    (permanentPolynomial n)
  have hy : (matchingVariableEquiv d).symm (d y) = .inl y :=
    (matchingVariableEquiv d).symm_apply_eq.mpr
      (matchingVariableEquiv_inl d y)
  have hderiv :
      MvPolynomial.pderiv (.inl y) (matchingMarkedPermanent d) =
        MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
          (MvPolynomial.pderiv (d y) (permanentPolynomial n)) := by
    change MvPolynomial.pderiv (.inl y)
      (MvPolynomial.rename (matchingVariableEquiv d).symm
        (permanentPolynomial n)) =
      MvPolynomial.rename (matchingVariableEquiv d).symm
        (MvPolynomial.pderiv (d y) (permanentPolynomial n))
    rw [← hy]
    exact hrename
  intro hzero
  apply permanentPolynomial_pderiv_ne_zero (d y).1 (d y).2
  apply (MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm).injective
  rw [map_zero]
  exact hderiv.symm.trans hzero
end PermanentFormulaLowerBound
