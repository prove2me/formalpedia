-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.four_mul_bitLift8_booleanXor_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:56:35.39845+00:00
-- url     : https://prove2.me/submissions/c3f25b1a-6ec5-4209-8675-8e548d91c90c

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_four_mul_bitLift8_booleanXor

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
theorem _root_.solution (xs ys : List (ZMod 2)) :
    4 * bitLift8 (booleanXor xs) * bitLift8 (booleanXor ys) =
      4 * (xs.map bitLift8).sum * (ys.map bitLift8).sum := by
  calc
    4 * bitLift8 (booleanXor xs) * bitLift8 (booleanXor ys) =
        (4 * (xs.map bitLift8).sum) * bitLift8 (booleanXor ys) := by
          rw [four_mul_bitLift8_booleanXor]
    _ = (xs.map bitLift8).sum *
        (4 * bitLift8 (booleanXor ys)) := by ring
    _ = (xs.map bitLift8).sum * (4 * (ys.map bitLift8).sum) := by
          rw [four_mul_bitLift8_booleanXor]
    _ = _ := by ring
end QEC.Distillation.Triorthogonal
