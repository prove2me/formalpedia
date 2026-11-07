-- Prove2me | solution 1 for QEC.QLDPC.semanticQuditDistance_le_of_nondetectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:53:51.9434+00:00
-- url     : https://prove2.me/submissions/76a288dc-1e2d-4e42-a594-46ddc9fc1467

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation

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
    (localOperator : Semantics.Operator region.selectedSystem)
    (hoperator : ¬ Semantics.DetectableOn code
      (region.extendLocalToRegister localOperator)) :
    semanticQuditDistance q code ≤ Fintype.card region.SelectedCoordinates := by
  apply Nat.sInf_le
  exact ⟨region, rfl, localOperator, hoperator⟩
end QEC.QLDPC
