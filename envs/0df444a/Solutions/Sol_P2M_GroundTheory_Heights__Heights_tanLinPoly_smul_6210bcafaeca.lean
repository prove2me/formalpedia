-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:15.098431+00:00
-- url     : https://prove2.me/submissions/21e02598-5b3c-46aa-9fd8-5e84b45b01bb

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
theorem _root_.solution (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by
  simp only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
end GroundTheory.Heights₂.Heights
