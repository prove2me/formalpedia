-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_trace_gaussQ_11da65445202
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:51.40412+00:00
-- url     : https://prove2.me/submissions/872e25eb-556b-4d6e-b91d-6405f71194a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_gaussBasis_zero_859cbc10225b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_gaussBasis_one_d101bba40995
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (z : GaussQ) : Algebra.trace ℚ GaussQ z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace gaussBasis, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
    Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    gaussBasis_zero, gaussBasis_one]
  change (![(z * 1).re, (z * 1).im] 0) + ![(z * ⟨0, 1⟩).re, (z * ⟨0, 1⟩).im] 1 = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, QuadraticAlgebra.im_mul]
  ring
end GroundTheory.Heights₂.Theta
