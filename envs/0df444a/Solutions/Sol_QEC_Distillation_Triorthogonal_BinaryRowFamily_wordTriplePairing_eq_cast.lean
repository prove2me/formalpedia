-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:32:05.965681+00:00
-- url     : https://prove2.me/submissions/b7d424db-d6d8-4a2d-982f-eda99a75e618

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_tripleOverlap_cast


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
    wordTriplePairing x y z = (tripleOverlap x y z : ZMod 2) := by
  rw [tripleOverlap_cast]
  rfl
end QEC.Distillation.Triorthogonal.BinaryRowFamily
