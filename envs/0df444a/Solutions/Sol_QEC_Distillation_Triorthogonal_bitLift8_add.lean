-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.bitLift8_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:49:27.74632+00:00
-- url     : https://prove2.me/submissions/5274588b-8194-4b3f-b355-965de707b904

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace QEC.Distillation.Triorthogonal
theorem _root_.solution (x y : ZMod 2) :
    bitLift8 (x + y) = bitLift8 x + bitLift8 y - 2 * bitLift8 x * bitLift8 y := by
  fin_cases x <;> fin_cases y <;> decide
end QEC.Distillation.Triorthogonal
