-- Prove2me | solution 1 for PermanentRollout.partitionFiberCoordinateEsymmPolynomial_succ_eq_deleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/e384b69b-38f5-4625-87a4-d3f1f2ea474b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_eval_deletedCoordinateEsymmPolynomial
import Theorems.Thm_PermanentRollout_coordinateEsymm_succ_eq_deleted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t q : ℕ) (i : Fin t) :
    partitionFiberCoordinateEsymmPolynomial t (q + 1) =
      deletedCoordinateEsymmPolynomial t (q + 1) i +
        MvPolynomial.X i * deletedCoordinateEsymmPolynomial t q i := by
  classical
  apply MvPolynomial.funext
  intro u
  have heval :
      MvPolynomial.eval u
          (partitionFiberCoordinateEsymmPolynomial t (q + 1)) =
        coordinateEsymm u (q + 1) := by
    rw [partitionFiberCoordinateEsymmPolynomial, MvPolynomial.esymm,
      coordinateEsymm, Finset.esymm_map_val]
    simp only [map_sum, map_prod, MvPolynomial.eval_X]
  simp only [map_add, map_mul, MvPolynomial.eval_X]
  rw [heval, eval_deletedCoordinateEsymmPolynomial,
    eval_deletedCoordinateEsymmPolynomial]
  exact coordinateEsymm_succ_eq_deleted u i q
end PermanentRollout
