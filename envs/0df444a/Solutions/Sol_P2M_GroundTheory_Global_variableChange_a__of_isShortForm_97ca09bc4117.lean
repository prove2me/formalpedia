-- Prove2me | solution 1 for P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:57.883015+00:00
-- url     : https://prove2.me/submissions/b69df179-fc9c-4e3c-b1ac-456fe5ada40b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_variableChange_rst_eq_zero
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
variable [CharZero F]
namespace GroundTheory.Global
theorem _root_.solution {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₄, hr, hs, ht]
end GroundTheory.Global
