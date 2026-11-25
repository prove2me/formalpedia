-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:26.900071+00:00
-- url     : https://prove2.me/submissions/e3d1b40e-d517-4ad8-9993-1caa6c25e678

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_finrank_sevenQ_3d28983f8fd9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : Fintype.card (QuadraticFieldSqrtNegSeven →+* ℂ) = 2 := by
  rw [NumberField.Embeddings.card, finrank_sevenQ]
end GroundTheory.Heights₂.Theta
