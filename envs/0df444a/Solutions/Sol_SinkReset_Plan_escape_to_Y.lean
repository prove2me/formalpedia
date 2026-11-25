-- Prove2me | solution 1 for SinkReset.Plan.escape_to_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:57.401868+00:00
-- url     : https://prove2.me/submissions/fd98ccca-873d-49c1-9c7f-5da1b2e12ef4

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
private theorem word_take {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.take i) :=
  fun a ha => hw a (List.mem_of_mem_take ha)
private theorem word_drop {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.drop i) :=
  fun a ha => hw a (List.mem_of_mem_drop ha)
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
theorem _root_.solution (hsc : SC A) (hne : (Y A).Nonempty) (x : Fin n)
    (hx : x ∈ Z A) :
    ∃ w, A.IsWord w ∧ w.length ≤ (Z A).card ∧ act w x ∈ Y A := by
  have hx0 : x ≠ 0 := ((mem_Z_iff A x).1 hx).1
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw, hwy⟩ := hsc x y hx0 ((mem_Y_iff A y).1 hy).1
  exact escape' A (Y A) (Z A) (mem_Y_iff A) (mem_Z_iff A) x ⟨w, hw, hwy ▸ hy⟩
end SinkReset.Plan
