-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:14.11985+00:00
-- url     : https://prove2.me/submissions/4da54d79-dcc5-4140-a1cb-f7e50843008c

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
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) : Q = nF ε := by
  have hc : Fintype.card (Fin Q) = Fintype.card {i // ¬ ε i = true} := by
    refine Fintype.card_congr (Equiv.ofBijective (fun j => ⟨e (Sum.inr j), by simp [h2 j]⟩) ⟨?_, ?_⟩)
    · intro a b hab
      have := congrArg Subtype.val hab
      simpa using this
    · rintro ⟨i, hi⟩
      cases hx : e.symm i with
      | inl a =>
        exfalso
        have h := h1 a
        rw [← hx, e.apply_symm_apply] at h
        exact hi h
      | inr b => exact ⟨b, Subtype.ext (by simp [← hx])⟩
  simpa [nF] using hc
end Formalism.BasicNotions.Examples₂.CD
