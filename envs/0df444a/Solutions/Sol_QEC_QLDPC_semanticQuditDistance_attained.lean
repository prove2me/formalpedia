-- Prove2me | solution 1 for QEC.QLDPC.semanticQuditDistance_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:54.928044+00:00
-- url     : https://prove2.me/submissions/5e69be7a-2d44-4f0e-a5f8-1aae15bc44b7

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
    (hnonempty : {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = weight ∧
        SupportsNondetectableLocalOperator code region}.Nonempty) :
    ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = semanticQuditDistance q code ∧
        SupportsNondetectableLocalOperator code region := by
  exact Nat.sInf_mem hnonempty
end QEC.QLDPC
