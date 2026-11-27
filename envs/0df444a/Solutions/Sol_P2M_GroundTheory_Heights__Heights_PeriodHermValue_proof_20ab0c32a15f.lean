-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodHermValue_proof_20ab0c32a15f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:21.554433+00:00
-- url     : https://prove2.me/submissions/e34e13bc-ee9c-405a-8a74-4345e8e93ed4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodHermValue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodHermValue_re_eq_3f09ef6ed02d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodHermValue_im_eq_c5f7a90330b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33


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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PeriodHermValue
theorem _root_.solution : PeriodHermValue.Statement := by
  intro g τ hY α β
  rw [MCSchur.hermValue_eq_qf, PeriodHermValue.re_eq, PeriodHermValue.im_eq,
    PeriodHermValue.qf_inv_mulVec _ hY]
end PeriodHermValue
end GroundTheory.Heights₂.Heights
