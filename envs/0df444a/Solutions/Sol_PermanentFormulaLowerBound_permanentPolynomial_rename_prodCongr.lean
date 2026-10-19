-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanentPolynomial_rename_prodCongr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/5bda8a12-7294-4024-93f9-a9951838aa0f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (r c : Equiv.Perm (Fin n)) :
    MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) = permanentPolynomial n := by
  classical
  let M := Matrix.mvPolynomialX (Fin n) (Fin n) ℂ
  have hmap :
      MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) =
          (M.submatrix r c).permanent := by
    simp [permanentPolynomial, M, Matrix.permanent,
      MvPolynomial.renameEquiv_apply, map_sum, map_prod]
  calc
    MvPolynomial.renameEquiv ℂ (Equiv.prodCongr r c)
        (permanentPolynomial n) =
      (M.submatrix r c).permanent := hmap
    _ = ((M.submatrix r id).submatrix id c).permanent := by rfl
    _ = (M.submatrix r id).permanent :=
      Matrix.permanent_permute_rows c (M.submatrix r id)
    _ = M.permanent := Matrix.permanent_permute_cols r M
    _ = permanentPolynomial n := rfl
end PermanentFormulaLowerBound
