-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.pairOverlap_cast8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:32:27.376682+00:00
-- url     : https://prove2.me/submissions/33227d2e-6774-49bd-a62f-7577cf526092

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
theorem _root_.solution (x y : Word (ZMod 2) Index) :
    (BinaryRowFamily.pairOverlap x y : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) := by
  classical
  rw [BinaryRowFamily.pairOverlap, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact bitLift8_mul (x p) (y p)
end QEC.Distillation.Triorthogonal
