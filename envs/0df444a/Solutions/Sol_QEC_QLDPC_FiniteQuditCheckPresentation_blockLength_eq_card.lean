-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:18.714203+00:00
-- url     : https://prove2.me/submissions/6da4c9bd-a61e-4be6-81f5-b2317fafcf3f

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheckPresentation
variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]
namespace QEC.QLDPC.FiniteQuditCheckPresentation
theorem _root_.solution (P : FiniteQuditCheckPresentation ι κ) :
    P.blockLength = Fintype.card ι :=
  rfl
end QEC.QLDPC.FiniteQuditCheckPresentation
