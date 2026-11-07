-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.distance_eq_semanticQuditDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:02.798671+00:00
-- url     : https://prove2.me/submissions/d39d75b0-5c69-4714-8425-142ce8dd846e

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_eq_semanticQuditDistance


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a = semanticQuditDistance
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize)
      (F.presentation a).code :=
  (F.presentation a).distance_eq_semanticQuditDistance
end QEC.QLDPC.QuantumCodeFamily
