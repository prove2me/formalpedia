-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.detectable_of_card_lt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:09.974517+00:00
-- url     : https://prove2.me/submissions/43ab691a-cef8-4b5c-b7fa-a3d7e6e3d9b9

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_detectable_of_card_lt_distance


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (a : A)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < F.distance a)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn (F.presentation a).code
      (region.extendLocalToRegister localOperator) :=
  (F.presentation a).detectable_of_card_lt_distance region hcard localOperator
end QEC.QLDPC.QuantumCodeFamily
