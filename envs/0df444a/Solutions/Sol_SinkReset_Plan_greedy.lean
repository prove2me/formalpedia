-- Prove2me | solution 1 for SinkReset.Plan.greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:11.872938+00:00
-- url     : https://prove2.me/submissions/8152c99e-895e-4f92-a3d8-711ec239651c

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_zero
public import Theorems.Thm_SinkReset_Plan_within_univ
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem kill_decreases' {n : ℕ} [NeZero n] (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ S.erase 0)
    (g : Fin n → Fin n) (hg : g 0 = 0) (hkill : g q = 0) :
    ((S.image g).erase 0).card + 1 ≤ (S.erase 0).card := by
  classical
  have hsub : (S.image g).erase 0 ⊆ ((S.erase 0).erase q).image g := by
    intro x hx
    obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hp⟩⟩, rfl⟩
    · rintro rfl; exact hx0 hkill
    · rintro rfl; exact hx0 hg
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hq] at h1
  have h2 : 0 < (S.erase 0).card := Finset.card_pos.2 ⟨q, hq⟩
  omega
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem active_card_le {n : ℕ} [NeZero n] (S : Finset (Fin n)) : (S.erase 0).card ≤ n - 1 := by
  calc (S.erase 0).card ≤ (Finset.univ.erase (0 : Fin n)).card :=
        Finset.card_le_card (Finset.erase_subset_erase _ (Finset.subset_univ _))
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
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
private theorem greedy' {n : ℕ} [NeZero n] (A : Automaton n) (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (b : ℕ) (hb : n - 1 ≤ b)
    (hT : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y →
      ∃ w, (A.IsWord w ∧ ∀ q ∈ T, act w q = 0) ∧ w.length + (n - 1 - T.card) ≤ b) :
    ∃ w, A.IsReset w ∧ w.length ≤ b := by
  classical
  suffices H : ∀ S : Finset (Fin n), ∃ w, A.IsWord w ∧ (∀ q ∈ S, act w q = 0) ∧
      w.length + (n - 1 - (S.erase 0).card) ≤ b by
    obtain ⟨w, hw, hw0, hlen⟩ := H Finset.univ
    rw [active_univ_card] at hlen
    exact ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, by omega⟩
  intro S
  induction hm : (S.erase 0).card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    by_cases hex : ∃ q ∈ S.erase 0, q ∉ Y
    · obtain ⟨q, hq, hqY⟩ := hex
      have hq0 := (Finset.mem_erase.1 hq).1
      have : ∃ a ∈ A.letters, a q = 0 := by
        by_contra hcon
        simp only [not_exists, not_and] at hcon
        exact hqY ((hY q).2 ⟨hq0, hcon⟩)
      obtain ⟨a, ha, haq⟩ := this
      have hdec := kill_decreases' S q hq a (A.sink_fixed a ha) haq
      obtain ⟨w', hw', hw'0, hlen'⟩ := ih _ (by omega) (S.image a) rfl
      have hle := active_card_le (n := n) S
      refine ⟨a :: w', (word_cons A).2 ⟨ha, hw'⟩, fun p hp => hw'0 _ (Finset.mem_image_of_mem _ hp), ?_⟩
      simp only [List.length_cons]
      omega
    · simp only [not_exists, not_and, not_not] at hex
      rcases (S.erase 0).eq_empty_or_nonempty with h | h
      · refine ⟨[], word_nil A, fun q hq => ?_, ?_⟩
        · by_contra hq0
          have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
          rw [h] at this; simp at this
        · rw [← hm, h]; simpa using hb
      · obtain ⟨w, ⟨hw, hw0⟩, hlen⟩ := hT (S.erase 0) h hex
        refine ⟨w, hw, fun q hq => ?_, by rw [← hm]; exact hlen⟩
        by_cases hq0 : q = 0
        · rw [hq0]; exact act_zero A w hw
        · exact hw0 q (Finset.mem_erase.2 ⟨hq0, hq⟩)
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
theorem _root_.solution (b : ℕ) (hb : n - 1 ≤ b)
    (hY : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y A →
      ∃ w, ResetOn A T w ∧ w.length + (n - 1 - T.card) ≤ b) :
    Within A Finset.univ b :=
  (within_univ A b).2 (greedy' A (Y A) (mem_Y_iff A) b hb hY)
end SinkReset.Plan
