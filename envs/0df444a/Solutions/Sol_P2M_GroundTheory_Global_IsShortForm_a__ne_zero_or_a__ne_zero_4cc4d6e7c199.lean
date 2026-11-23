-- Prove2me | solution 1 for P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.505907+00:00
-- url     : https://prove2.me/submissions/b8677b95-b11d-4ffa-9389-1138be16b40c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38
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



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
namespace GroundTheory.Global
namespace IsShortForm
theorem _root_.solution {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  have := W.isUnit_Δ.ne_zero
  rw [hW.Δ_eq, h.1, h.2] at this
  simp at this
end IsShortForm
end GroundTheory.Global
