-- Prove2me | solution 1 for P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_c176d31fc2ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:23.525885+00:00
-- url     : https://prove2.me/submissions/0732f9c1-b1c0-4829-9dd1-f7007089c748

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero
attribute [local simp] GroundTheory.Global.weberFunction_some
attribute [local simp] GroundTheory.Global.weberFunction_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
namespace GroundTheory.Global
theorem _root_.solution {W : WeierstrassCurve F} (hb : W.a₆ = 0) : automorphismOrder W = 4 := by
  simp [automorphismOrder, hb]
end GroundTheory.Global
