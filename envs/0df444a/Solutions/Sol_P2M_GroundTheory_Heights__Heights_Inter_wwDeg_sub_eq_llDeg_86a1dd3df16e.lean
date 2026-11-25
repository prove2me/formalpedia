-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:56.286018+00:00
-- url     : https://prove2.me/submissions/a3049071-fbc2-4a8c-82b1-b7a214477c64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (n : ℕ) :
    (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg := by
  funext k
  cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg]
end GroundTheory.Heights₂.Heights.Inter
