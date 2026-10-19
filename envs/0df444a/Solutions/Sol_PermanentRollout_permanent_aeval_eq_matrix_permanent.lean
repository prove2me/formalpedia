-- Prove2me | solution 1 for PermanentRollout.permanent_aeval_eq_matrix_permanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/c113dae6-62ca-4316-aa2d-2ee58f50c68c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} {ι : Type*}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ)) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => A ij.1 ij.2)
      (permanent n) = Matrix.permanent A := by
  classical
  simp only [permanent, Matrix.permanent, map_sum, map_prod,
    MvPolynomial.aeval_X]
end PermanentRollout
