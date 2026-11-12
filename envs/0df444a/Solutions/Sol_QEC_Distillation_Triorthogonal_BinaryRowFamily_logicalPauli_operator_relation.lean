-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPauli_operator_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:21:19.679676+00:00
-- url     : https://prove2.me/submissions/859f43fd-40de-47d1-adba-a5055a00dad2

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalXPauli_commutes_logicalZPauli_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes


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
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a b : OddRow) :
    PauliSymplectic.toQubitOperator (R.logicalXPauli a) *
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) =
      if a = b then
        -(PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a))
      else
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a) := by
  classical
  by_cases hab : a = b
  · rw [if_pos hab]
    exact PauliSymplectic.toQubitOperator_anticommute_of_not_commutes _ _
      (by
        intro hcomm
        exact (R.logicalXPauli_commutes_logicalZPauli_iff hR a b).1 hcomm hab)
  · rw [if_neg hab]
    exact PauliSymplectic.toQubitOperator_commute_of_commutes _ _
      ((R.logicalXPauli_commutes_logicalZPauli_iff hR a b).2 hab)
end QEC.Distillation.Triorthogonal.BinaryRowFamily
