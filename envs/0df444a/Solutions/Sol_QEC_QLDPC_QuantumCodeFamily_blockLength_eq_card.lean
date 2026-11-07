-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:52.925508+00:00
-- url     : https://prove2.me/submissions/18ef7886-cf4a-4a30-82a9-ba9ecafad36a

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card



set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (a : A) :
    F.blockLength a = Fintype.card (ι a) :=
  (F.presentation a).blockLength_eq_card
end QEC.QLDPC.QuantumCodeFamily
