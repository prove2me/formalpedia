-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:35:37.235761+00:00
-- url     : https://prove2.me/submissions/d006dbda-a6c5-4dec-88a9-2603fa3c7752

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
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution (x y z : Word (ZMod 2) Col) :
    wordTriplePairing x y z = wordTriplePairing z x y := by
  classical
  apply Finset.sum_congr rfl
  intro p _hp
  ring
end QEC.Distillation.Triorthogonal.BinaryRowFamily
