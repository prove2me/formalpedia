-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:26.861337+00:00
-- url     : https://prove2.me/submissions/1c8703fd-b9d1-4581-ba27-358bcd0b5298

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
theorem _root_.solution (P : FiniteQuditCheckPresentation ι κ)
    (checkIndex : κ) (coordinate : ι) :
    P.incidence.incident checkIndex coordinate ↔
      coordinate ∈ (P.checks checkIndex).region.selected :=
  Iff.rfl
end QEC.QLDPC.FiniteQuditCheckPresentation
