-- Prove2me | solution 1 for SinkReset.Plan.cycle_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:33.886507+00:00
-- url     : https://prove2.me/submissions/eb7234c3-5dd5-4707-9960-cfd140c76a4b

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
private theorem pot_perm {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (hg : Function.Injective g)
    (p : Fin n) (hle : ∀ q, q ≠ p → weight q ≤ weight (g q)) (hp : weight p ≤ weight (g p) + 1)
    (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  rw [Finset.sum_image (fun x _ y _ h => hg h)]
  calc ∑ q ∈ S, weight q ≤ ∑ q ∈ S, (weight (g q) + if q = p then 1 else 0) :=
        Finset.sum_le_sum fun q _ => by
          by_cases h : q = p
          · subst h; simpa using hp
          · simpa [h] using hle q h
    _ = ∑ q ∈ S, weight (g q) + ∑ q ∈ S, (if q = p then 1 else 0) := Finset.sum_add_distrib
    _ ≤ ∑ q ∈ S, weight (g q) + 1 := by
        refine Nat.add_le_add_left ?_ _
        rw [Finset.sum_ite_eq']
        split_ifs <;> simp
private theorem pot_kill {n : ℕ} (weight : Fin n → ℕ) (g : Fin n → Fin n) (p : Fin n)
    (hfix : ∀ q, q ≠ p → g q = q) (hp : weight p ≤ 1) (S : Finset (Fin n)) :
    ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image g, weight q + 1 := by
  classical
  have hsub : S.erase p ⊆ S.image g := fun q hq => by
    obtain ⟨hqp, hq⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_image.2 ⟨q, hq, hfix q hqp⟩
  have h1 := Finset.sum_le_sum_of_subset (f := weight) hsub
  by_cases hpS : p ∈ S
  · rw [← Finset.add_sum_erase S weight hpS]; omega
  · rw [Finset.erase_eq_of_notMem hpS] at h1; omega
private theorem shift_val {k m : ℕ} (q : Fin (k + m + 1)) :
    (shift k m q).val = if q.val = 0 then 0 else q.val % (k + m) + 1 := by
  by_cases h : q = 0
  · subst h; simp [shift]
  · have h' : q.val ≠ 0 := fun h'' => h (Fin.ext (by simp [h'']))
    simp [shift, h, h']
private theorem shift_val_pos {k m : ℕ} (q : Fin (k + m + 1)) (hq : q.val ≠ 0) :
    (shift k m q).val = if q.val < k + m then q.val + 1 else 1 := by
  have := q.isLt
  rw [shift_val, if_neg hq]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [show q.val = k + m by omega, Nat.mod_self]
private theorem shift_injective {k m : ℕ} : Function.Injective (shift k m) := by
  intro x y hxy
  have h := congrArg Fin.val hxy
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0
  · omega
  · rw [shift_val x, if_pos hx0, shift_val_pos y hy0] at h; split_ifs at h <;> omega
  · rw [shift_val y, if_pos hy0, shift_val_pos x hx0] at h; split_ifs at h <;> omega
  · rw [shift_val_pos x hx0, shift_val_pos y hy0] at h; split_ifs at h <;> omega
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
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters)
    (S : Finset (Fin (k + m + 1))) :
    potential (cycleWeight k m) S ≤ potential (cycleWeight k m) (S.image a) + 1 := by
  unfold potential
  rcases ha with h | ⟨i, hi2, hik, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨one, hone⟩ : ∃ one : Fin (k + m + 1), one.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    refine pot_perm _ (shift k m) shift_injective one (fun q hq => ?_) ?_ S
    · have hq1 : q.val ≠ 1 := fun h => hq (Fin.ext (h.trans hone.symm))
      have := q.isLt
      rw [cw_val, cw_val, shift_val]
      by_cases hq0 : q.val = 0
      · simp [hq0]
      · rw [if_neg hq0]
        rcases Nat.lt_or_ge q.val (k + m) with h | h
        · rw [Nat.mod_eq_of_lt h]; split_ifs <;> first | contradiction | omega
        · rw [show q.val = k + m by omega, Nat.mod_self]; split_ifs <;> first | contradiction | omega
    · rw [cw_val, cw_val, shift_val, hone, Nat.mod_eq_of_lt (by omega : 1 < k + m)]
      split_ifs <;> first | contradiction | omega
  · refine pot_kill _ (kill i) i (fun q hq => if_neg hq) ?_ S
    rw [cw_val]
    split_ifs <;> omega
end SinkReset.Plan
