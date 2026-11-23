-- Prove2me | solution 1 for P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:38.788993+00:00
-- url     : https://prove2.me/submissions/547f19bf-1d5a-491d-9445-72d1ff0e165c

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
theorem _root_.solution {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by
  simp [weberValue, ha, hb]
end GroundTheory.Global
