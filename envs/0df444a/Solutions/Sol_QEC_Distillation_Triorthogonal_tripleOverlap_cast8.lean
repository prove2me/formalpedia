-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.tripleOverlap_cast8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:49:31.004713+00:00
-- url     : https://prove2.me/submissions/8b06cbaa-74a9-48e8-958d-c02d3043361a

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
theorem _root_.solution (x y z : Word (ZMod 2) Index) :
    (BinaryRowFamily.tripleOverlap x y z : ZMod 8) =
      ∑ p, bitLift8 (x p) * bitLift8 (y p) * bitLift8 (z p) := by
  classical
  rw [BinaryRowFamily.tripleOverlap, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  change bitLift8 (x p * y p * z p) =
    bitLift8 (x p) * bitLift8 (y p) * bitLift8 (z p)
  rw [bitLift8_mul, bitLift8_mul]
end QEC.Distillation.Triorthogonal
