-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheckPresentation.localityProfile_eq_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:41:28.328201+00:00
-- url     : https://prove2.me/submissions/b2b1dbda-78f9-4614-ac1f-7d3c3aae75e7

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
    P.localityProfile = P.incidence.localityProfile :=
  rfl
end QEC.QLDPC.FiniteQuditCheckPresentation
