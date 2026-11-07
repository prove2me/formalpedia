-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.exists_blockLength_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:56.515901+00:00
-- url     : https://prove2.me/submissions/dce30363-2e4e-4c11-b6d5-c1f3434d4b90

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (N : Nat) :
    ∃ a : A, N ≤ F.blockLength a :=
  F.cofinal_blockLength N
end QEC.QLDPC.QuantumCodeFamily
