-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tanLinPoly_zero_a4dc94d63023
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:02.178863+00:00
-- url     : https://prove2.me/submissions/010817bf-342c-40d5-bd69-8118c723cfd6

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
theorem _root_.solution (p : Fin n → ℂ) : tanLinPoly p 0 = 0 := by
  simp [tanLinPoly]
end GroundTheory.Heights₂.Heights
