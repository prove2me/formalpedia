-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.distance_eq_semanticQuditDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:07.877901+00:00
-- url     : https://prove2.me/submissions/6dae4cf2-a892-4159-88bc-62770bf418b5

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
theorem _root_.solution
    (P : FiniteQuditCheckPresentation ι κ) :
    P.distance = semanticQuditDistance
      (uniformQuditDimensions (ι := ι) P.alphabetSize) P.code :=
  rfl
end QEC.QLDPC.FiniteQuditCheckPresentation
