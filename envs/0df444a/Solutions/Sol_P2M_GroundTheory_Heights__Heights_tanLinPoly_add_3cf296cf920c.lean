-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:06.664743+00:00
-- url     : https://prove2.me/submissions/f97ccf69-e0a7-45fe-9290-b62a05d8cf24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by
  simp only [tanLinPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end GroundTheory.Heights₂.Heights
