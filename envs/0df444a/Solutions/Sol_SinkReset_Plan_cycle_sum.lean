-- Prove2me | solution 1 for SinkReset.Plan.cycle_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:35.336433+00:00
-- url     : https://prove2.me/submissions/2ec13180-7fcc-446b-8877-d5d0e2cf5916

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
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
private theorem cw_val {k m : ℕ} (q : Fin (k + m + 1)) :
    cycleWeight k m q = if q.val = 0 then 0 else if 2 ≤ q.val ∧ q.val ≤ k + 1 then 1 else 2 := by
  by_cases h : q = 0
  · subst h; simp [cycleWeight]
  · have h' : q.val ≠ 0 := fun h'' => h (Fin.ext (by simp [h'']))
    simp [cycleWeight, h, h']
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
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    potential (cycleWeight k m) Finset.univ = k + 2 * m := by
  obtain ⟨wt, hwt⟩ : ∃ wt : ℕ → ℕ, ∀ v, wt v = if v = 0 then 0 else if 2 ≤ v ∧ v ≤ k + 1 then 1 else 2 :=
    ⟨_, fun _ => rfl⟩
  have hcw : ∀ q, cycleWeight k m q = wt q.val := fun q => by rw [cw_val, hwt]
  have wt0 : wt 0 = 0 := by rw [hwt, if_pos rfl]
  have wt1 : wt 1 = 2 := by rw [hwt]; split_ifs <;> omega
  have wtK : ∀ v, 2 ≤ v → v ≤ k + 1 → wt v = 1 := fun v h1 h2 => by
    rw [hwt]; split_ifs <;> omega
  have wtO : ∀ v, k + 1 < v → wt v = 2 := fun v h1 => by
    rw [hwt]; split_ifs <;> omega
  unfold potential
  rw [Finset.sum_congr rfl fun q _ => hcw q, Fin.sum_univ_eq_sum_range wt (k + m + 1)]
  have h1 : ∀ s, s ≤ k → ∑ i ∈ Finset.range (s + 2), wt i = s + 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [Finset.sum_range_succ, Finset.sum_range_one, wt0, wt1]
    | succ s ih =>
      intro hs
      have e1 : ∑ i ∈ Finset.range (s + 1 + 2), wt i =
          ∑ i ∈ Finset.range (s + 2), wt i + wt (s + 2) := Finset.sum_range_succ wt (s + 2)
      rw [e1, ih (by omega), wtK (s + 2) (by omega) (by omega)]
  have h2 : ∀ t, t ≤ m - 1 → ∑ i ∈ Finset.range (k + 2 + t), wt i = k + 2 + 2 * t := by
    intro t
    induction t with
    | zero => intro _; exact h1 k le_rfl
    | succ t ih =>
      intro ht
      have e1 : ∑ i ∈ Finset.range (k + 2 + (t + 1)), wt i =
          ∑ i ∈ Finset.range (k + 2 + t), wt i + wt (k + 2 + t) :=
        Finset.sum_range_succ wt (k + 2 + t)
      rw [e1, ih (by omega), wtO _ (by omega)]
      ring
  rw [show k + m + 1 = k + 2 + (m - 1) by omega, h2 (m - 1) le_rfl]
  omega
end SinkReset.Plan
