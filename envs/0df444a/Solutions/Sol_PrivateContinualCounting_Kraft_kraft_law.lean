-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.kraft_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:45:05.794161+00:00
-- url     : https://prove2.me/submissions/d5154411-004b-4a2f-9b0e-808dad711e46

import Theorems.Thm_PrivateContinualCounting_Kraft_lti_divergence
import Theorems.Thm_PrivateContinualCounting_Kraft_fixed_period
import Theorems.Thm_PrivateContinualCounting_Kraft_kraft_necessity
import Theorems.Thm_PrivateContinualCounting_Kraft_kraft_sufficiency
import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

open PrivateContinualCounting.Kraft

theorem solution :
    ((∀ (m : ℕ) (M : LTICounter m), LogSqDiverges M.val.variance) ∧
      (∀ (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀),
        LogSqDiverges M.counter.variance)) ∧
    (∀ (g : ℝ → ℝ), IsEnvelope g →
      ((∃ (m : ℕ) (M : LTICounter m), HasEnvelope M.val.variance g) ↔ KraftCondition g) ∧
      (KraftCondition g → ∃ M : LTICounter 1, HasEnvelope M.val.variance g)) := by
  refine ⟨⟨fun m M => (lti_divergence.1 m M.val M.property).2,
    fun p I₀ _ M => fixed_period p I₀ M⟩, fun g hg => ⟨⟨?_, ?_⟩, kraft_sufficiency g hg⟩⟩
  · rintro ⟨m, M, hM⟩
    obtain ⟨D, _, hg1, hgm, _⟩ := hg
    exact kraft_necessity m M.val M.property g hg1 hgm hM
  · intro hK
    obtain ⟨M, hM⟩ := kraft_sufficiency g hg hK
    exact ⟨1, M, hM⟩
