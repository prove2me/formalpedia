-- Prove2me | solution 1 for SinkReset.Plan.no_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:09.561794+00:00
-- url     : https://prove2.me/submissions/a22bcc13-43b7-4093-9658-93c11d21e600

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
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem word_single {n : ℕ} [NeZero n] (A : Automaton n) {a : Letter n} (ha : a ∈ A.letters) : A.IsWord [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  exact hb ▸ ha
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
private theorem mem_Y_of_dist {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (p : Fin n) : p ∈ Y ↔ 2 ≤ d p := by
  rw [hY]
  constructor
  · rintro ⟨hp0, hpa⟩
    by_contra hlt
    rcases Nat.lt_succ_iff.1 (Nat.not_le.1 hlt) |>.lt_or_eq with h | h
    · exact hp0 (dist_eq_zero hd (by omega))
    · obtain ⟨a, ha, had⟩ := dist_step hd (j := 0) h
      exact hpa a ha (dist_eq_zero hd had)
  · intro h2
    refine ⟨fun hp0 => ?_, fun a ha hap => ?_⟩
    · rw [hp0, dist_zero hd] at h2; omega
    · have := (hd p).2 [a] (word_single A ha) hap
      simp at this; omega
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
theorem _root_.solution (hk : 2 ≤ k) (hA : A.IsAk k) {d : Fin n → ℕ}
    (hd : Distances A d) (y₁ y₂ : Fin n) (hY : Y A = {y₁, y₂})
    (h₁ : d y₁ = 2) (h₂ : d y₂ = 3) :
    (∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂) ∧
    (∃ c ∈ A.letters, c y₂ = y₁) ∧
    (∀ a ∈ A.letters, a y₁ ≠ y₂) := by
  unfold Distances at hd
  have hmemT : ∀ q, q ∈ Y A ↔ q = y₁ ∨ q = y₂ := by
    intro q; rw [hY]; simp
  have hy₂ : y₂ ∈ Y A := (hmemT y₂).2 (Or.inr rfl)
  have hmap : ∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂ := by
    intro a ha
    have := dist_le_succ hd y₂ ha
    exact (hmemT _).1 ((mem_Y_of_dist hd (Y A) (mem_Y_iff A) _).2 (by omega))
  refine ⟨hmap, ?_, ?_⟩
  · obtain ⟨c, hc, hcd⟩ := dist_step hd (q := y₂) (j := 2) h₂
    refine ⟨c, hc, ?_⟩
    rcases hmap c hc with h | h
    · exact h
    · rw [h] at hcd; omega
  · intro b hb hby
    refine trap A {y₂} (Finset.singleton_nonempty _) ?_ ?_ hA
    · rw [Finset.mem_singleton]
      exact fun h => ((mem_Y_iff A y₂).1 hy₂).1 h.symm
    · intro t ht x hx
      rw [Finset.mem_singleton] at ht
      subst ht
      rcases hmap x hx with h | h
      · refine ⟨[b], word_single A hb, by simp only [List.length_singleton]; omega, ?_⟩
        change b (x t) ∈ _
        rw [h, hby]; exact Finset.mem_singleton_self _
      · refine ⟨[], word_nil A, by simp only [List.length_nil]; omega, ?_⟩
        change x t ∈ _
        rw [h]; exact Finset.mem_singleton_self _
end SinkReset.Plan
