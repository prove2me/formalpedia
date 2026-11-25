-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormEval_proof_90bb5aef2d2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:06.289546+00:00
-- url     : https://prove2.me/submissions/3f994f1a-3156-4ebe-bac7-2a521ce2ffdb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormFormEval
theorem _root_.solution : NormFormEval.Statement := by
  intro R A _ _ _ _ _ n x u
  classical
  let b := Module.Free.chooseBasis R A
  let M : Fin n → Matrix (Module.Free.ChooseBasisIndex R A) (Module.Free.ChooseBasisIndex R A) R :=
    fun j => Algebra.leftMulMatrix b (x j)
  rw [normForm_eq_det b, RingHom.map_det]
  have hev : (MvPolynomial.eval u).mapMatrix (∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C) =
      Algebra.leftMulMatrix b (∑ j, algebraMap R A (u j) * x j) := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, eval_X, eval_C, M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
  rw [hev, ← Algebra.norm_eq_matrix_det b]
end NormFormEval
end GroundTheory.Heights₂.Heights.Vertical
