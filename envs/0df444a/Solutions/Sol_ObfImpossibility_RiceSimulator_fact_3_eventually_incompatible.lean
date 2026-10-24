-- Prove2me | solution 1 for ObfImpossibility.RiceSimulator.fact_3_eventually_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:56:38.974285+00:00
-- url     : https://prove2.me/submissions/c4420c65-aace-4cd0-a24b-5ed742c2a961

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting
namespace ObfImpossibility.RiceSimulator

/-- Fact (3), p. A:41: if `[M] ≢ [N]` then there is `n'` such that `N` is not
`n`-compatible with `M` for all `n > n'`. -/
theorem _root_.solution (M N : Machine) (h : fn M ≠ fn N) :
    ∃ n' : ℕ, ∀ n : ℕ, n' < n → ¬ Compatible n N M := by
  classical
  have hx : ∃ t x : ℕ, bounded N t x ≠ bounded M t x := by
    by_contra hnone
    push_neg at hnone
    apply h
    funext x
    apply Part.ext
    intro y
    change y ∈ M.eval x ↔ y ∈ N.eval x
    rw [Nat.Partrec.Code.evaln_complete, Nat.Partrec.Code.evaln_complete]
    have heq : ∀ t, M.evaln t x = N.evaln t x := fun t => (hnone t x).symm
    simp only [heq]
  obtain ⟨t, x, hneq⟩ := hx
  refine ⟨max t (Nat.size x), ?_⟩
  intro n hn hc
  exact hneq (hc t x (le_trans (le_max_left _ _) (Nat.le_of_lt hn))
    (le_trans (le_max_right _ _) (Nat.le_of_lt hn)))


end ObfImpossibility.RiceSimulator
