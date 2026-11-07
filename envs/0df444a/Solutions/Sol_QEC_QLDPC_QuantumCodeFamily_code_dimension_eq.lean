-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.code_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:58.606205+00:00
-- url     : https://prove2.me/submissions/73536d54-c620-4d04-9400-4091b909319a

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_semantic_dimension_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (a : A) :
    (F.presentation a).code.dimension =
      (F.presentation a).alphabetSize ^ F.encodedDimension a :=
  (F.presentation a).semantic_dimension_eq
end QEC.QLDPC.QuantumCodeFamily
