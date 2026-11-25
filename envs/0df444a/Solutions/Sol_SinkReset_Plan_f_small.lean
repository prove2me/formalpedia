-- Prove2me | solution 1 for SinkReset.Plan.f_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:37.849124+00:00
-- url     : https://prove2.me/submissions/68506430-ac77-4f7e-988e-fb0c289585a8

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
private theorem f_succ (k n : ℕ) : f k (n + 1) = f k n + (n + k - 1) / k := by
  unfold f
  exact Finset.sum_range_succ _ _
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k n : ℕ} (hk : 1 ≤ k) (hn : n ≤ k + 1) :
    f k n = n - 1 := by
  induction n with
  | zero => simp [f]
  | succ n ih =>
    rw [f_succ, ih (by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [zero_add]
      rw [Nat.div_eq_of_lt (by omega)]
    · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      omega
end SinkReset.Plan
