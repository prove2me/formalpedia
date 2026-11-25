-- Prove2me | solution 1 for SinkReset.Plan.cycle_reset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:40.326609+00:00
-- url     : https://prove2.me/submissions/d685feff-5d50-4373-bbb2-db60ae97897f

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
public import Theorems.Thm_SinkReset_Plan_act_zero
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
private theorem act_map_kill {n : ℕ} [NeZero n] (L : List (Fin n)) (q : Fin n) :
    act (L.map kill) q = if q ∈ L then 0 else q := by
  induction L generalizing q with
  | nil => simp [act]
  | cons i L ih =>
    rw [List.map_cons]
    change act (L.map kill) (kill i q) = _
    by_cases hqi : q = i
    · rw [hqi, show kill i i = 0 from if_pos rfl, ih]
      simp
    · rw [show kill i q = q from if_neg hqi, ih]
      simp [hqi]
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
    ∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m := by
  obtain ⟨two, htwo⟩ : ∃ two : Fin (k + m + 1), two.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have hkill2 : kill two ∈ (cycle k m).letters := Or.inr ⟨two, by omega, by omega, rfl⟩
  have hsh : shift k m ∈ (cycle k m).letters := Or.inl rfl
  obtain ⟨Ks, hKs⟩ : ∃ Ks : List (Fin (k + m + 1)),
      Ks = (List.finRange k).map (fun j => ⟨j.val + 2, by have := j.isLt; omega⟩) := ⟨_, rfl⟩
  have hmemK : ∀ q : Fin (k + m + 1), q ∈ Ks ↔ 2 ≤ q.val ∧ q.val ≤ k + 1 := by
    intro q
    rw [hKs, List.mem_map]
    constructor
    · rintro ⟨j, _, rfl⟩
      have := j.isLt
      show 2 ≤ j.val + 2 ∧ j.val + 2 ≤ k + 1
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨q.val - 2, by omega⟩, List.mem_finRange _, Fin.ext ?_⟩
      show q.val - 2 + 2 = q.val
      omega
  obtain ⟨round, hround⟩ : ∃ r : List (Letter (k + m + 1)), r = [shift k m, kill two] := ⟨_, rfl⟩
  have hword_rep : ∀ r, (cycle k m).IsWord (List.replicate r round).flatten := by
    intro r a ha
    rw [List.mem_flatten] at ha
    obtain ⟨l, hl, hal⟩ := ha
    rw [List.mem_replicate] at hl
    rw [hl.2, hround] at hal
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hal
    rcases hal with rfl | rfl
    · exact hsh
    · exact hkill2
  have hlen_rep : ∀ r, ((List.replicate r round).flatten).length = 2 * r := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, hround]
      simp only [List.length_cons, List.length_nil]
      omega
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (k + m + 1) → ℕ, ∀ q,
      δ q = if q.val = 1 then 1 else if k + 1 < q.val then k + m + 2 - q.val else 0 :=
    ⟨_, fun _ => rfl⟩
  have hrounds : ∀ r : ℕ, ∀ q : Fin (k + m + 1), (q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m)) →
      δ q ≤ r → act (List.replicate r round).flatten q = 0 := by
    intro r
    induction r with
    | zero =>
      intro q hq hd
      exfalso
      rw [hδ] at hd
      split_ifs at hd <;> omega
    | succ r ih =>
      intro q hq hd
      have hr1 : act round q = kill two (shift k m q) := by rw [hround]; rfl
      rw [List.replicate_succ, List.flatten_cons, act_append, hr1]
      have hq0 : q.val ≠ 0 := by omega
      have hsv := shift_val_pos (k := k) (m := m) q hq0
      by_cases h1 : q.val = 1
      · have : shift k m q = two := Fin.ext (by rw [hsv, htwo]; split_ifs <;> omega)
        rw [this, show kill two two = 0 from if_pos rfl]
        exact act_zero _ _ (hword_rep r)
      · have hne : shift k m q ≠ two := fun h => by
          have := congrArg Fin.val h
          rw [hsv, htwo] at this
          split_ifs at this <;> omega
        rw [show kill two (shift k m q) = shift k m q from if_neg hne]
        have := q.isLt
        refine ih _ ?_ ?_
        · rw [hsv]; split_ifs <;> omega
        · rw [hδ] at hd ⊢
          rw [hsv]
          split_ifs at hd ⊢ <;> omega
  have hw1 : (cycle k m).IsWord (Ks.map kill) := by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact Or.inr ⟨i, ((hmemK i).1 hi).1, ((hmemK i).1 hi).2, rfl⟩
  refine ⟨Ks.map kill ++ (List.replicate m round).flatten,
    ⟨(word_append _ _ _).2 ⟨hw1, hword_rep m⟩, fun q => ?_⟩, ?_⟩
  · rw [act_append, act_map_kill]
    split_ifs with hqK
    · exact act_zero _ _ (hword_rep m)
    · by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext (by simp [hq0])
        rw [this]; exact act_zero _ _ (hword_rep m)
      · have := q.isLt
        have hnK := (hmemK q).not.1 hqK
        refine hrounds m q (by omega) ?_
        rw [hδ]
        split_ifs <;> omega
  · rw [List.length_append, List.length_map, hlen_rep, hKs, List.length_map, List.length_finRange]
end SinkReset.Plan
