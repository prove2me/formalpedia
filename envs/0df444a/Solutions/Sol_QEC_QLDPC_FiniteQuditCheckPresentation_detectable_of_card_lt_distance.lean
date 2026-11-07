-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.detectable_of_card_lt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:41:27.565611+00:00
-- url     : https://prove2.me/submissions/949e2626-98b4-4dde-b411-c82e7ec1c6e0

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Theorems.Thm_QEC_QLDPC_detectable_of_card_lt_semanticQuditDistance

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]
namespace QEC.QLDPC.FiniteQuditCheckPresentation
theorem _root_.solution
    (P : FiniteQuditCheckPresentation ι κ)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι) P.alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < P.distance)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn P.code
      (region.extendLocalToRegister localOperator) := by
  exact detectable_of_card_lt_semanticQuditDistance
    P.code region hcard localOperator
end QEC.QLDPC.FiniteQuditCheckPresentation
