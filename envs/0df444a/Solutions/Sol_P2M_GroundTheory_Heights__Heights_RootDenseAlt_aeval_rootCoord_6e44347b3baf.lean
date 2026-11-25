-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_rootCoord_6e44347b3baf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:28:26.773314+00:00
-- url     : https://prove2.me/submissions/5566bbcb-90a8-4a54-b1eb-d7b4385069f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootDenseAlt
namespace GroundTheory.Heights₂.Heights.RootDenseAlt
theorem _root_.solution {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by
  rw [show aeval x (aeval (grassPolyCoord f j m) g) =
      ((aeval x).restrictScalars ℤ).comp (aeval (grassPolyCoord f j m)) g from rfl, comp_aeval]
  exact congrArg (fun y => aeval y g) (funext fun p => (aeval_grassPolyCoord x p).symm)
end GroundTheory.Heights₂.Heights.RootDenseAlt
