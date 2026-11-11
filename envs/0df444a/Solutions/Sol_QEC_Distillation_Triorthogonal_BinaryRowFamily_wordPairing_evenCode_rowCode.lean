-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.wordPairing_evenCode_rowCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:26:11.29027+00:00
-- url     : https://prove2.me/submissions/a047f760-d04f-4ac1-b5ea-7359757c78d6

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
    {x y : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    (hy : y ∈ R.rowCode.carrier) : wordPairing x y = 0 := by
  apply wordPairing_span_left R.evenRow y (fun b => ?_) hx
  apply wordPairing_span_right R.row (R.evenRow b) (fun a => ?_) hy
  rcases a with a | a
  · exact R.evenRow_oddRow_pairing hR b a
  · exact R.evenRow_pairing hR b a
end QEC.Distillation.Triorthogonal.BinaryRowFamily
