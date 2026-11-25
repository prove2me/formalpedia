-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:19.968169+00:00
-- url     : https://prove2.me/submissions/6e6baa1c-2739-4da1-bc49-e0494addeca8

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : P = nT ε := by
  have hc : Fintype.card (Fin P) = Fintype.card {i // ε i = true} := by
    refine Fintype.card_congr (Equiv.ofBijective (fun i => ⟨e (Sum.inl i), h1 i⟩) ⟨?_, ?_⟩)
    · intro a b hab
      have := congrArg Subtype.val hab
      simpa using this
    · rintro ⟨i, hi⟩
      cases hx : e.symm i with
      | inl a => exact ⟨a, Subtype.ext (by simp [← hx])⟩
      | inr b =>
        exfalso
        have h := h2 b
        rw [← hx, e.apply_symm_apply] at h
        simp [hi] at h
  simpa [nT] using hc
end Formalism.BasicNotions.Examples₂.CD
