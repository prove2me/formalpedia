-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesLineDegree_single_injective_ea33b9403e45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:06.405828+00:00
-- url     : https://prove2.me/submissions/7b86ea88-4459-4814-bc10-a305d5fc0382

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree

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
open NumberField Matrix
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesLineDegree
variable {K : Type} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KLinesLineDegree
theorem _root_.solution (x : Fin n) :
    Function.Injective (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  intro s t h
  simpa using congrFun h x
end GroundTheory.Heights₂.Heights.KLinesLineDegree
