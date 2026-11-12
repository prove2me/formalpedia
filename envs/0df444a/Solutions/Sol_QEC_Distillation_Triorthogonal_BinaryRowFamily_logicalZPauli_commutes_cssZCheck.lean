-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssZCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:20:48.354991+00:00
-- url     : https://prove2.me/submissions/0d308875-3f02-498f-b5a2-ed29060f469b

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    (z : Word (ZMod 2) Col) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssZCheck z) :=
  PauliSymplectic.cssZCheck_commutes_cssZCheck _ _
end QEC.Distillation.Triorthogonal.BinaryRowFamily
