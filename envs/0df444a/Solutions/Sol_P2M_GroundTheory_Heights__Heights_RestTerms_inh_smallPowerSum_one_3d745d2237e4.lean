-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_smallPowerSum_one_3d745d2237e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:20.00664+00:00
-- url     : https://prove2.me/submissions/19fe023a-9e88-486f-a2be-bd93e71acee5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (τ : Fin 1) : smallPowerSum 1 1 1 .last 1 τ = flagTwoSecondRoot := by
  fin_cases τ
  simp [smallPowerSum, yRoot, yIndex, SmallBlock.sign]
end GroundTheory.Heights₂.Heights.RestTerms
