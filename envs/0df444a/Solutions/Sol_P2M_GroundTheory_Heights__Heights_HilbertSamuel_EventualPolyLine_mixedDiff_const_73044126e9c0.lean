-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:26.373727+00:00
-- url     : https://prove2.me/submissions/3c5bc66e-ac97-4b07-8aeb-cadb363eef1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
theorem _root_.solution (D : ℕ) (a : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (fun _ : Fin D => a) f = (List.replicate D a).foldr diffStep f := by
  simp only [mixedDiff, List.ofFn_const]
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
