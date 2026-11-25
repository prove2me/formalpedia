-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYdd7.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:50.466861+00:00
-- url     : https://prove2.me/submissions/aae5ea37-a029-447f-a4e8-288238e62ffe

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYdd7
theorem _root_.solution :
    ∀ {l : ℕ} (f : ℕ → ℚ),
      (∀ (k : ℕ), f (k + l) = f k) → ∀ (a : ℕ), ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k := by
  intro l f hf a
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => f (n + k)) l
    have h2 := Finset.sum_range_succ' (fun k => f (n + k)) l
    have h3 : f (n + l) = f n := hf n
    have h4 : ∑ k ∈ Finset.range l, f (n + 1 + k) = ∑ k ∈ Finset.range l, f (n + (k + 1)) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_assoc, add_comm 1 k])
    simp only [add_zero] at h2
    rw [h4]
    linarith
end UpperTheory.Reformulated.B.DYdd7
