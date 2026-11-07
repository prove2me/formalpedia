-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.distance_le_blockLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:27:19.433459+00:00
-- url     : https://prove2.me/submissions/8566941c-6063-437a-b402-0e3ab5c1e1fc

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_le_blockLength


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a ≤ F.blockLength a :=
  (F.presentation a).distance_le_blockLength
end QEC.QLDPC.QuantumCodeFamily
