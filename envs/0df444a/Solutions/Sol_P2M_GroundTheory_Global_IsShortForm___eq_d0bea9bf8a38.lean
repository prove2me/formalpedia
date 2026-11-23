-- Prove2me | solution 1 for P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:59.336307+00:00
-- url     : https://prove2.me/submissions/a96426bd-3e79-42d0-be73-32242800c996

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
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
theorem _root_.solution {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]
  ring
end IsShortForm
end GroundTheory.Global
