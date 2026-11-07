-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.alphabetSize_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:53:54.43995+00:00
-- url     : https://prove2.me/submissions/4ea73b71-42e0-4a40-87eb-29ee4757e44c

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
    0 < P.alphabetSize :=
  lt_of_lt_of_le (by decide) P.alphabetSize_ge_two
end QEC.QLDPC.FiniteQuditCheckPresentation
