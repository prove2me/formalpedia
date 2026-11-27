-- Prove2me | solution 2 for P2M_GroundTheory_Global_IsShortForm___eq_g_50a215210837
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:23.778813+00:00
-- url     : https://prove2.me/submissions/010739f6-b3a0-4f0e-9c71-c0ec1bbe2e0e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
namespace GroundTheory.Global
namespace IsShortForm
theorem _root_.solution {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = g₂ W ^ 3 - 27 * g₃ W ^ 2 := by
  rw [hW.Δ_eq, g₂, g₃]
  ring
end IsShortForm
end GroundTheory.Global
