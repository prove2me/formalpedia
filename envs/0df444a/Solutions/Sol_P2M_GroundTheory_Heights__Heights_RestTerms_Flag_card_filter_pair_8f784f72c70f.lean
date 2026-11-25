-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:07.653362+00:00
-- url     : https://prove2.me/submissions/ba7e6539-d759-4605-afec-cbca7033c982

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution {f N : ℕ} (s : Finset (Fin N)) (τ : Fin f) (v : Fin f × Fin N) :
    (s.filter fun i => ((τ, i) : Fin f × Fin N) = v).card = if v.1 = τ ∧ v.2 ∈ s then 1 else 0 := by
  rcases v with ⟨σ, j⟩
  by_cases h : σ = τ ∧ j ∈ s
  · obtain ⟨rfl, hj⟩ := h
    rw [if_pos ⟨rfl, hj⟩, Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Prod.mk.injEq, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨hj, rfl⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi heq
    simp only [Prod.mk.injEq] at heq
    exact h ⟨heq.1.symm, heq.2 ▸ hi⟩
end GroundTheory.Heights₂.Heights.RestTerms.Flag
