-- Prove2me | solution 1 for SinkReset.Plan.short_kill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:14.281611+00:00
-- url     : https://prove2.me/submissions/be8e8928-1f3f-4318-88ac-b771d10d858b

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem active_card_le {n : ℕ} [NeZero n] (S : Finset (Fin n)) : (S.erase 0).card ≤ n - 1 := by
  calc (S.erase 0).card ≤ (Finset.univ.erase (0 : Fin n)).card :=
        Finset.card_le_card (Finset.erase_subset_erase _ (Finset.subset_univ _))
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
private theorem dist_exists {n : ℕ} [NeZero n] (A : Automaton n) (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) :
    ∃ d : Fin n → ℕ, ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length := by
  classical
  have hP : ∀ q, ∃ ℓ, ∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = ℓ := fun q => by
    obtain ⟨w, hw, hw0⟩ := h q
    exact ⟨_, w, hw, hw0, rfl⟩
  refine ⟨fun q => Nat.find (hP q), fun q => ⟨Nat.find_spec (hP q), fun w hw hw0 => ?_⟩⟩
  exact Nat.find_min' (hP q) ⟨w, hw, hw0, rfl⟩
private theorem dist_zero {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) : d 0 = 0 := by
  have := (hd 0).2 [] (word_nil A) rfl
  simpa using this
private theorem dist_eq_zero {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) {q : Fin n} (h : d q = 0) : q = 0 := by
  obtain ⟨w, _, hw0, hlen⟩ := (hd q).1
  rw [h] at hlen
  rw [List.eq_nil_of_length_eq_zero hlen] at hw0
  exact hw0
private theorem dist_le_succ {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (q : Fin n) {a : Letter n} (ha : a ∈ A.letters) :
    d q ≤ d (a q) + 1 := by
  obtain ⟨w, hw, hw0, hlen⟩ := (hd (a q)).1
  have := (hd q).2 (a :: w) ((word_cons A).2 ⟨ha, hw⟩) hw0
  simpa [hlen] using this
private theorem dist_step {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) {q : Fin n} {j : ℕ} (h : d q = j + 1) :
    ∃ a ∈ A.letters, d (a q) = j := by
  obtain ⟨w, hw, hw0, hlen⟩ := (hd q).1
  cases w with
  | nil => simp at hlen; omega
  | cons a w =>
    rw [word_cons] at hw
    refine ⟨a, hw.1, ?_⟩
    have h1 := (hd (a q)).2 w hw.2 hw0
    have h2 := dist_le_succ hd q hw.1
    simp only [List.length_cons] at hlen
    omega
private theorem dist_chain {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (j : ℕ) :
    ∀ t (q : Fin n), d q = j + t → ∃ p, d p = j := by
  intro t
  induction t with
  | zero => intro q hq; exact ⟨q, hq⟩
  | succ t ih =>
    intro q hq
    obtain ⟨a, _, ha⟩ := dist_step hd (j := j + t) (by rw [hq]; ring)
    exact ih _ ha
private theorem card_le_of_values {n : ℕ} [NeZero n] (d : Fin n → ℕ) (X : Finset (Fin n)) (lo hi : ℕ)
    (hex : ∀ j, lo ≤ j → j ≤ hi → ∃ p, d p = j)
    (hX : ∀ p, lo ≤ d p → d p ≤ hi → p ∈ X) : hi + 1 - lo ≤ X.card := by
  classical
  let c : ℕ → Fin n := fun j => if h : lo ≤ j ∧ j ≤ hi then Classical.choose (hex j h.1 h.2) else 0
  have hc : ∀ j ∈ Finset.Icc lo hi, d (c j) = j := by
    intro j hj
    have h := Finset.mem_Icc.1 hj
    simp only [c, dif_pos h]
    exact Classical.choose_spec (hex j h.1 h.2)
  rw [← Nat.card_Icc]
  refine Finset.card_le_card_of_injOn c ?_ ?_
  · intro j hj
    have h := Finset.mem_Icc.1 hj
    exact hX _ (by rw [hc j hj]; exact h.1) (by rw [hc j hj]; exact h.2)
  · intro i hi j hj hij
    have := congrArg d hij
    rwa [hc i hi, hc j hj] at this
private theorem short_kill' {n : ℕ} [NeZero n] (A : Automaton n) {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (S : Finset (Fin n))
    (hne : (S.erase 0).Nonempty) :
    ∃ q ∈ S.erase 0, ∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length ≤ n - (S.erase 0).card := by
  classical
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (S.erase 0) d hne
  obtain ⟨w, hw, hw0, hlen⟩ := (hd q).1
  refine ⟨q, hq, w, hw, hw0, ?_⟩
  have hq0 : d q ≠ 0 := fun h => (Finset.mem_erase.1 hq).1 (dist_eq_zero hd h)
  have hcount := card_le_of_values d (insert 0 (S.erase 0))ᶜ 1 (d q - 1)
    (fun j _ hj => dist_chain hd j (d q - j) q (by omega))
    (fun p h1 h2 => by
      rw [Finset.mem_compl, Finset.mem_insert, not_or]
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · rw [hp, dist_zero hd] at h1; omega
      · have := hmin p hp; omega)
  rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp), Fintype.card_fin] at hcount
  have := active_card_le (n := n) S
  omega
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
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
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (h : ∃ w, A.IsReset w) (S : Finset (Fin n))
    (hne : (active S).Nonempty) :
    ∃ q ∈ active S, ∃ w, A.IsWord w ∧ act w q = 0 ∧
      w.length ≤ n - (active S).card := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := h
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q⟩
  exact short_kill' A hd S hne
end SinkReset.Plan
