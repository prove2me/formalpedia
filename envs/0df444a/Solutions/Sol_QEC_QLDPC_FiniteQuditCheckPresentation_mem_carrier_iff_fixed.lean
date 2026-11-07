-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.mem_carrier_iff_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:08.953324+00:00
-- url     : https://prove2.me/submissions/5cf533a8-88ac-408b-b27a-ac48e3cc5b46

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
    (ψ : Semantics.Qudit.QuditRegister
      (uniformQuditDimensions (ι := ι) P.alphabetSize)) :
    ψ ∈ P.code.carrier ↔
      ∀ checkIndex, (P.checks checkIndex).globalOperator ψ = ψ :=
  P.carrier_iff_fixed ψ
end QEC.QLDPC.FiniteQuditCheckPresentation
