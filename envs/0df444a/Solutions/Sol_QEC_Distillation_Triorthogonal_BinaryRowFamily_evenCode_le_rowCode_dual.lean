-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.evenCode_le_rowCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:00:54.429348+00:00
-- url     : https://prove2.me/submissions/87135a7e-9453-4e97-be6e-b87eeec0ce35

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordPairing_evenCode_rowCode

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
    R.evenCode.carrier ≤ R.rowCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro y hy
  exact R.wordPairing_evenCode_rowCode hR hx hy
end QEC.Distillation.Triorthogonal.BinaryRowFamily
