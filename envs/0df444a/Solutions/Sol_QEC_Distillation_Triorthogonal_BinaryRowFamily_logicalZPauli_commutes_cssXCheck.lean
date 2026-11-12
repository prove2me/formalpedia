-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalZPauli_commutes_cssXCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:20:52.122688+00:00
-- url     : https://prove2.me/submissions/8420a98b-3ab5-4b66-aefa-e2a5f69e5520

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
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a : OddRow) {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssXCheck x) :=
  PauliSymplectic.cssZCheck_commutes_cssXCheck_of_mem_dual R.evenCode hx
    (R.oddCode_le_evenCode_dual hR (R.oddRow_mem_oddCode a))
end QEC.Distillation.Triorthogonal.BinaryRowFamily
