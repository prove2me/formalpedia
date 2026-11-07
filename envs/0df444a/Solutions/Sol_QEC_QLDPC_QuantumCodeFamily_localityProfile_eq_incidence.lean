-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.localityProfile_eq_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:14.522635+00:00
-- url     : https://prove2.me/submissions/c78af1db-4543-4431-9f45-6337cd6d3f0a

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_localityProfile_eq_incidence


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (a : A) :
    F.localityProfile a = (F.presentation a).incidence.localityProfile :=
  (F.presentation a).localityProfile_eq_incidence
end QEC.QLDPC.QuantumCodeFamily
