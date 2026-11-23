-- Prove2me | solution 1 for P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:38.884318+00:00
-- url     : https://prove2.me/submissions/bb9439e1-d175-4106-8d98-b4798c8453e8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero


attribute [local simp] GroundTheory.Global.weberFunction_zero
attribute [local simp] GroundTheory.Global.weberFunction_some

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
namespace GroundTheory.Global
theorem _root_.solution {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by
  simp [weberValue, hb]
end GroundTheory.Global
