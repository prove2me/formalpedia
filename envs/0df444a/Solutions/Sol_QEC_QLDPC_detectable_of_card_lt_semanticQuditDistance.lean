-- Prove2me | solution 1 for QEC.QLDPC.detectable_of_card_lt_semanticQuditDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:59.298846+00:00
-- url     : https://prove2.me/submissions/d33d84e4-66c9-4d5b-9432-dc15a064dd5a

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Theorems.Thm_QEC_QLDPC_semanticQuditDistance_le_of_nondetectable

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
namespace QEC.QLDPC
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (region : Semantics.QuditSubsystem q)
    (hcard : Fintype.card region.SelectedCoordinates <
      semanticQuditDistance q code)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator) := by
  by_contra hoperator
  have hle := semanticQuditDistance_le_of_nondetectable
    code region localOperator hoperator
  omega
end QEC.QLDPC
