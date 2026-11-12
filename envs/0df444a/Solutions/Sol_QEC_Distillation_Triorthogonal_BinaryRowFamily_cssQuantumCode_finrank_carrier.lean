-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.cssQuantumCode_finrank_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:01:52.832161+00:00
-- url     : https://prove2.me/submissions/7bf83911-8389-4b20-b5e1-6d747a3464ca

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier


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
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Module.finrank Complex R.cssQuantumCode.carrier = 2 ^ Fintype.card OddRow := by
  rw [cssQuantumCode,
    PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier,
    R.cssLogicalExponent_eq_card_oddRows hR]
end QEC.Distillation.Triorthogonal.BinaryRowFamily
