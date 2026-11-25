-- Prove2me | solution 1 for SinkReset.Plan.cycle_loses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:51.496348+00:00
-- url     : https://prove2.me/submissions/3e01186d-48fb-44ac-8c1c-928649ba77f8

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_trap
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
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
private theorem cyc_iter {k m : ℕ} (hkm : 0 < k + m) (e : Letter (k + m + 1))
    (he : ∀ q : Fin (k + m + 1), (e q).val = if q.val = 0 then 0 else q.val % (k + m) + 1)
    (q : Fin (k + m + 1)) (hq : q.val ≠ 0) :
    ∀ s, (e^[s] q).val = (q.val - 1 + s) % (k + m) + 1 := by
  intro s
  induction s with
  | zero =>
    have := q.isLt
    rw [Function.iterate_zero_apply, add_zero, Nat.mod_eq_of_lt (by omega)]
    omega
  | succ s ih =>
    rw [Function.iterate_succ_apply', he, ih, if_neg (Nat.succ_ne_zero _), Nat.mod_add_mod,
      show q.val - 1 + s + 1 = q.val - 1 + (s + 1) by omega]
private theorem act_replicate {n : ℕ} (e : Letter n) (r : ℕ) (q : Fin n) :
    act (List.replicate r e) q = e^[r] q := by
  induction r generalizing q with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ]
    change act (List.replicate r e) (e q) = _
    rw [ih, Function.iterate_succ_apply]
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
    ¬ (cycle k m).IsAk (k + 1) := by
  have hkm : 0 < k + m := by omega
  refine trap _ (Finset.univ.filter (fun q : Fin (k + m + 1) => q.val = 1 ∨ k + 1 < q.val))
    ⟨⟨1, by omega⟩, by simp⟩ (by simp) ?_
  intro t ht a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  have ht0 : t.val ≠ 0 := by omega
  have := t.isLt
  rcases ha with h | ⟨i, hi2, hik, rfl⟩
  · rw [Set.mem_singleton_iff] at h
    subst h
    by_cases ht1 : t.val = 1
    · refine ⟨List.replicate k (shift k m), fun b hb => ?_, by simp, ?_⟩
      · rw [List.mem_replicate] at hb
        rw [hb.2]; exact Or.inl rfl
      · have hv : (act (shift k m :: List.replicate k (shift k m)) t).val = (k + 1) % (k + m) + 1 := by
          change (act (List.replicate k (shift k m)) (shift k m t)).val = _
          rw [act_replicate, show (shift k m)^[k] (shift k m t) = (shift k m)^[k + 1] t from
            (Function.iterate_succ_apply _ _ _).symm, cyc_iter hkm _ shift_val t ht0 (k + 1), ht1,
            Nat.sub_self, zero_add]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hv]
        rcases Nat.lt_or_ge (k + 1) (k + m) with h | h
        · right; rw [Nat.mod_eq_of_lt h]; omega
        · left; rw [show k + m = k + 1 by omega, Nat.mod_self]
    · refine ⟨[], word_nil _, by simp, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (shift k m t).val = 1 ∨ k + 1 < (shift k m t).val
      rw [shift_val_pos t ht0]
      split_ifs <;> omega
  · refine ⟨[], word_nil _, by simp, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hti : t ≠ i := fun h => by subst h; omega
    change (kill i t).val = 1 ∨ k + 1 < (kill i t).val
    rw [show kill i t = t from if_neg hti]
    exact ht
end SinkReset.Plan
