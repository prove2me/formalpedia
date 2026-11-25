-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_exists_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:51.520963+00:00
-- url     : https://prove2.me/submissions/499d98aa-a25f-4888-91a8-d151d078aecd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (f : ℕ → Bool) :
    ∀ d a : ℕ, f a ≠ f (a + d) → ∃ c, a ≤ c ∧ c < a + d ∧ f c ≠ f (c + 1) := by
  intro d
  induction d with
  | zero =>
    intro a h
    simp at h
  | succ d ih =>
    intro a h
    by_cases h1 : f a = f (a + d)
    · refine ⟨a + d, by omega, by omega, ?_⟩
      rw [← h1]
      simpa [Nat.add_assoc] using h
    · obtain ⟨c, h2, h3, h4⟩ := ih a h1
      exact ⟨c, h2, by omega, h4⟩
end ReciprocityTheory.ChartRestriction.DS.Lap
