-- Prove2me | solution 1 for PermanentRollout.sum_deletedCoordinateEsymmPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/95f4f2c8-31c7-4b76-a17a-6d084f6ab2f2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_eval_deletedCoordinateEsymmPolynomial
import Theorems.Thm_PermanentRollout_sum_deletedCoordinateEsymm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (t q : ℕ) :
    (∑ i : Fin t, deletedCoordinateEsymmPolynomial t q i) =
      MvPolynomial.C ((t - q : ℕ) : ℂ) *
        partitionFiberCoordinateEsymmPolynomial t q := by
  classical
  apply MvPolynomial.funext
  intro u
  have heval :
      MvPolynomial.eval u
          (partitionFiberCoordinateEsymmPolynomial t q) =
        coordinateEsymm u q := by
    rw [partitionFiberCoordinateEsymmPolynomial, MvPolynomial.esymm,
      coordinateEsymm, Finset.esymm_map_val]
    simp only [map_sum, map_prod, MvPolynomial.eval_X]
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  simp_rw [eval_deletedCoordinateEsymmPolynomial]
  rw [heval]
  exact sum_deletedCoordinateEsymm u q
end PermanentRollout
