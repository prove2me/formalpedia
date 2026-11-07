-- Prove2me | solution 1 for QEC.QLDPC.hasUniformLDPC_iff_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:15.594403+00:00
-- url     : https://prove2.me/submissions/2acc02cc-e94e-4520-85f8-eed76bb56a41

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_boundedLocality_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC
theorem _root_.solution (F : QuantumCodeFamily A ι κ) :
    HasUniformLDPC F ↔
      ∃ B : Nat, ∀ a, F.maxCheckWeight a ≤ B ∧ F.maxVariableDegree a ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun a => (F.boundedLocality_iff a B).mp (hB a)⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, fun a => (F.boundedLocality_iff a B).mpr (hB a)⟩
end QEC.QLDPC
