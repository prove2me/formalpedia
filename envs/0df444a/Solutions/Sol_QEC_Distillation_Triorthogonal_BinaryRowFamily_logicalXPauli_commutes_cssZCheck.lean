-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalXPauli_commutes_cssZCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:20:45.048246+00:00
-- url     : https://prove2.me/submissions/7e29290c-b130-4e73-b955-35c0180d34ef

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
    {z : Word (ZMod 2) Col} (hz : z ∈ R.rowCode.dual.carrier) :
    PauliSymplectic.Commutes (R.logicalXPauli a)
      (PauliSymplectic.cssZCheck z) :=
  PauliSymplectic.cssXCheck_commutes_cssZCheck_of_mem_dual R.rowCode
    (R.row_mem_rowCode (.inl a)) hz
end QEC.Distillation.Triorthogonal.BinaryRowFamily
