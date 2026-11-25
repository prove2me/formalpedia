-- Prove2me | solution 1 for SinkReset.Plan.f_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:49.714977+00:00
-- url     : https://prove2.me/submissions/1c0e6f73-9505-40a3-b6cd-fa97e005da65

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_f_small
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
private theorem f_cycle' {k m : ℕ} (hk : 1 ≤ k) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by
  induction m with
  | zero => rw [f_small hk (by omega)]; omega
  | succ m ih =>
    rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, f_succ, ih (by omega),
      Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]
    omega
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
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by
  exact f_cycle' hk hmk
end SinkReset.Plan
