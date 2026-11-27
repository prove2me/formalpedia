-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormFormEval_proof_08cac4a28981
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:38.047023+00:00
-- url     : https://prove2.me/submissions/92b5d5bf-e454-4ed4-b391-99f0ccedaa73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormFormEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace NormFormEval
theorem _root_.solution : NormFormEval.Statement := by
  intro R S _ _ _ _ _ n η u
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R S)]
  unfold normForm
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
end NormFormEval
end GroundTheory.Heights₂.Heights
