-- Prove2me | solution 1 for P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:57.453003+00:00
-- url     : https://prove2.me/submissions/a56288b5-dc43-4829-8a7b-564a26cf37da

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
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₆, hr, ht]
end GroundTheory.Global
