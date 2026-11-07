-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.semantic_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:42.780573+00:00
-- url     : https://prove2.me/submissions/cce0ff1c-b468-40de-9805-3fe74e27b1e6

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
    P.code.dimension = P.alphabetSize ^ P.encodedQudits :=
  P.dimension_eq
end QEC.QLDPC.FiniteQuditCheckPresentation
