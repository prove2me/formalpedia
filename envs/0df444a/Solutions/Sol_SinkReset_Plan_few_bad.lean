-- Prove2me | solution 1 for SinkReset.Plan.few_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:04.534123+00:00
-- url     : https://prove2.me/submissions/94b3ba9d-4280-4fd5-bc60-098d4c054a44

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
public import Theorems.Thm_SinkReset_Plan_act_zero
public import Theorems.Thm_SinkReset_Plan_trap
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem word_take {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.take i) :=
  fun a ha => hw a (List.mem_of_mem_take ha)
private theorem word_drop {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.drop i) :=
  fun a ha => hw a (List.mem_of_mem_drop ha)
private theorem active_univ_card {n : ℕ} [NeZero n] : ((Finset.univ : Finset (Fin n)).erase 0).card = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
private theorem mem_Z_iff {n : ℕ} [NeZero n] (A : Automaton n) (q : Fin n) :
    q ∈ Z A ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0 := by
  unfold Z
  simp
private theorem mem_Y_iff {n : ℕ} [NeZero n] (A : Automaton n) (q : Fin n) :
    q ∈ Y A ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0 := by
  show q ∈ (Finset.univ.erase 0) \ Z A ↔ _
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 h
    have h0 := (Finset.mem_erase.1 h1).1
    exact ⟨h0, fun a ha haq => h2 ((mem_Z_iff A q).2 ⟨h0, a, ha, haq⟩)⟩
  · rintro ⟨h0, h⟩
    refine Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨h0, Finset.mem_univ _⟩, fun hz => ?_⟩
    obtain ⟨_, a, ha, haq⟩ := (mem_Z_iff A q).1 hz
    exact h a ha haq
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
private theorem escape' {n : ℕ} [NeZero n] (A : Automaton n) (Y Z : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0)
    (x : Fin n) (hreach : ∃ w, A.IsWord w ∧ act w x ∈ Y) :
    ∃ w, A.IsWord w ∧ w.length ≤ Z.card ∧ act w x ∈ Y := by
  classical
  have hP : ∃ ℓ, ∃ w, A.IsWord w ∧ act w x ∈ Y ∧ w.length = ℓ := by
    obtain ⟨w, hw, hwY⟩ := hreach
    exact ⟨_, w, hw, hwY, rfl⟩
  obtain ⟨w, hw, hwY, hlen⟩ := Nat.find_spec hP
  set L := Nat.find hP with hL
  refine ⟨w, hw, ?_, hwY⟩
  have hY0 : ∀ y ∈ Y, y ≠ 0 := fun y hy => ((hY y).1 hy).1
  have hsplit : ∀ i, act w x = act (w.drop i) (act (w.take i) x) := by
    intro i
    rw [← act_append, List.take_append_drop]
  rw [← Finset.card_range w.length]
  refine Finset.card_le_card_of_injOn (fun i => act (w.take i) x) ?_ ?_
  · intro i hi
    have hi : i < w.length := Finset.mem_range.1 hi
    simp only [Finset.mem_coe]
    rw [hZ]
    have hne : act (w.take i) x ≠ 0 := by
      intro h0
      apply hY0 _ hwY
      rw [hsplit i, h0, act_zero A _ (word_drop A hw i)]
    refine ⟨hne, ?_⟩
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hmem : act (w.take i) x ∈ Y := (hY _).2 ⟨hne, hcon⟩
    have := Nat.find_min' hP ⟨w.take i, word_take A hw i, hmem, rfl⟩
    rw [List.length_take] at this
    omega
  · -- a repeated state would give a shortcut
    have key : ∀ i j, i < j → j < w.length → act (w.take i) x ≠ act (w.take j) x := by
      intro i j hlt hj hij
      have hword : A.IsWord (w.take i ++ w.drop j) :=
        (word_append A _ _).2 ⟨word_take A hw i, word_drop A hw j⟩
      have hact : act (w.take i ++ w.drop j) x ∈ Y := by
        rw [act_append, hij, ← hsplit j]; exact hwY
      have := Nat.find_min' hP ⟨_, hword, hact, rfl⟩
      rw [List.length_append, List.length_take, List.length_drop] at this
      omega
    intro i hi j hj hij
    simp only at hij
    have hi : i < w.length := Finset.mem_range.1 hi
    have hj : j < w.length := Finset.mem_range.1 hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i j hlt hj hij
    · exact key j i hlt hi hij.symm
private theorem few_bad' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hA : A.IsAk k)
    (hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q)
    (Y Z : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0) :
    (Y.Nonempty → k ≤ Z.card) ∧ Y.card ≤ n - 1 - k := by
  have h1 : Y.Nonempty → k ≤ Z.card := by
    intro hne
    by_contra hlt
    apply trap A Y hne (fun h0 => ((hY 0).1 h0).1 rfl) _ hA
    intro t ht a ha
    have hat : a t ≠ 0 := ((hY t).1 ht).2 a ha
    by_cases hY' : a t ∈ Y
    · exact ⟨[], word_nil A, by simp only [List.length_nil]; omega, hY'⟩
    · obtain ⟨y, hy⟩ := hne
      have hreach : ∃ w, A.IsWord w ∧ act w (a t) ∈ Y := by
        obtain ⟨w, hw, hwy⟩ := hsc (a t) y hat ((hY y).1 hy).1
        exact ⟨w, hw, hwy ▸ hy⟩
      obtain ⟨u, hu, hlen, huY⟩ := escape' A Y Z hY hZ (a t) hreach
      exact ⟨u, hu, by omega, huY⟩
  refine ⟨h1, ?_⟩
  have hdisj : Disjoint Y Z := Finset.disjoint_left.2 fun q hqY hqZ => by
    obtain ⟨_, a, ha, h⟩ := (hZ q).1 hqZ
    exact ((hY q).1 hqY).2 a ha h
  have hsub : Y ∪ Z ⊆ Finset.univ.erase 0 := by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact Finset.mem_erase.2 ⟨((hY q).1 h).1, Finset.mem_univ _⟩
    · exact Finset.mem_erase.2 ⟨((hZ q).1 h).1, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, active_univ_card] at hc
  rcases Y.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  · have := h1 h; omega
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
variable {n k : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (hk : 1 ≤ k) (hA : A.IsAk k) (hsc : SC A) :
    ((Y A).Nonempty → k ≤ (Z A).card) ∧ (Y A).card ≤ n - 1 - k :=
  few_bad' A hA hsc (Y A) (Z A) (mem_Y_iff A) (mem_Z_iff A)
end SinkReset.Plan
