-- Prove2me | solution 1 for SinkReset.Plan.two_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:33.470784+00:00
-- url     : https://prove2.me/submissions/adccb702-ee43-40d1-ad1c-1127c62306e0

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
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem wins_word' {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, A.IsWord w ∧ ∀ q ∈ S, act w q = 0 := by
  induction h with
  | reset S hS => exact ⟨[], word_nil A, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (word_nil A) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, (word_cons A).2 ⟨ha, hw⟩, fun q hq => ?_⟩
    exact hw0 _ (Finset.mem_image_of_mem _ hq)
private theorem word_single {n : ℕ} [NeZero n] (A : Automaton n) {a : Letter n} (ha : a ∈ A.letters) : A.IsWord [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  exact hb ▸ ha
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
private theorem dist_le_Y {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (q : Fin n) : d q ≤ Y.card + 1 := by
  have := card_le_of_values d Y 2 (d q) (fun j _ hj => dist_chain hd j (d q - j) q (by omega))
    (fun p h1 _ => (mem_Y_of_dist hd Y hY p).2 h1)
  omega
private theorem dist_two_of_Y {n : ℕ} [NeZero n] {A : Automaton n} {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hne : Y.Nonempty) : ∃ y ∈ Y, d y = 2 := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image Y d hne
  have h2 := (mem_Y_of_dist hd Y hY y).1 hy
  refine ⟨y, hy, ?_⟩
  by_contra hne2
  obtain ⟨a, _, had⟩ := dist_step hd (q := y) (j := d y - 1) (by omega)
  have := hmin (a y) ((mem_Y_of_dist hd Y hY (a y)).2 (by omega))
  omega
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
private theorem two_bad' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hk : 2 ≤ k) (hA : A.IsAk k)
    {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length)
    (Y : Finset (Fin n)) (hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0)
    (hcard : Y.card ≤ 2) (T : Finset (Fin n)) (hT : T ⊆ Y) (hsize : T.card = 2) :
    ∃ w, (A.IsWord w ∧ ∀ q ∈ T, act w q = 0) ∧ w.length ≤ 4 := by
  classical
  have hTY : T = Y := Finset.eq_of_subset_of_card_le hT (by omega)
  subst hTY
  obtain ⟨y₁, hy₁, hd₁⟩ := dist_two_of_Y hd T hY (Finset.card_pos.1 (by omega))
  have hpair : ∃ y₂, y₂ ≠ y₁ ∧ T = {y₁, y₂} := by
    obtain ⟨x, y, hxy, hT2⟩ := Finset.card_eq_two.1 hsize
    rw [hT2] at hy₁
    rcases Finset.mem_insert.1 hy₁ with rfl | h
    · exact ⟨y, Ne.symm hxy, hT2⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact ⟨x, hxy, by rw [hT2, Finset.pair_comm]⟩
  obtain ⟨y₂, hne, hT2⟩ := hpair
  have hmemT : ∀ q, q ∈ T ↔ q = y₁ ∨ q = y₂ := by
    intro q; rw [hT2]; simp
  have hy₂ : y₂ ∈ T := (hmemT y₂).2 (Or.inr rfl)
  -- states outside `T` are at distance at most one
  have hsmall : ∀ r, r ∉ T → d r ≤ 1 := fun r hr => by
    by_contra h
    exact hr ((mem_Y_of_dist hd T hY r).2 (by omega))
  have hd₂ : 2 ≤ d y₂ ∧ d y₂ ≤ 3 :=
    ⟨(mem_Y_of_dist hd T hY y₂).1 hy₂, by have := dist_le_Y hd T hY y₂; omega⟩
  have hdist_le : ∀ r, r ≠ y₂ → d r ≤ 2 := fun r hr => by
    by_cases hrT : r ∈ T
    · rcases (hmemT r).1 hrT with rfl | rfl
      · omega
      · exact absurd rfl hr
    · have := hsmall r hrT; omega
  obtain ⟨w₁, hw₁, hw₁0, hlw₁⟩ := (hd y₁).1
  rcases Nat.lt_or_ge (d y₂) 3 with h3 | h3
  · -- both states of `T` at distance two: every state is at distance at most two
    have hall : ∀ r, d r ≤ 2 := fun r => by
      by_cases hr : r = y₂
      · rw [hr]; omega
      · exact hdist_le r hr
    obtain ⟨w₂, hw₂, hw₂0, hlw₂⟩ := (hd (act w₁ y₂)).1
    refine ⟨w₁ ++ w₂, ⟨(word_append A _ _).2 ⟨hw₁, hw₂⟩, fun q hq => ?_⟩, ?_⟩
    · rw [act_append]
      rcases (hmemT q).1 hq with rfl | rfl
      · rw [hw₁0]; exact act_zero A w₂ hw₂
      · exact hw₂0
    · rw [List.length_append, hlw₁, hlw₂]
      have := hall (act w₁ y₂); omega
  · -- `d y₂ = 3`: Lemma 7
    have hd₂3 : d y₂ = 3 := by omega
    have hmap : ∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂ := by
      intro a ha
      have := dist_le_succ hd y₂ ha
      exact (hmemT _).1 ((mem_Y_of_dist hd T hY _).2 (by omega))
    obtain ⟨c, hc, hcd⟩ := dist_step hd (q := y₂) (j := 2) hd₂3
    have hcy : c y₂ = y₁ := by
      rcases hmap c hc with h | h
      · exact h
      · rw [h] at hcd; omega
    have hno : ∀ a ∈ A.letters, a y₁ ≠ y₂ := by
      intro b hb hby
      refine trap A {y₂} (Finset.singleton_nonempty _) ?_ ?_ hA
      · rw [Finset.mem_singleton]
        exact fun h => ((hY y₂).1 hy₂).1 h.symm
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
    have hy₁Y := (hY y₁).1 hy₁
    have hz0 : c y₁ ≠ 0 := hy₁Y.2 c hc
    have hz2 : c y₁ ≠ y₂ := hno c hc
    by_cases hz1 : c y₁ = y₁
    · refine ⟨c :: w₁, ⟨(word_cons A).2 ⟨hc, hw₁⟩, fun q hq => ?_⟩, ?_⟩
      · rcases (hmemT q).1 hq with rfl | rfl
        · change act w₁ (c q) = 0; rw [hz1]; exact hw₁0
        · change act w₁ (c q) = 0; rw [hcy]; exact hw₁0
      · simp only [List.length_cons]; omega
    · have hzT : c y₁ ∉ T := fun h => by
        rcases (hmemT _).1 h with h | h
        · exact hz1 h
        · exact hz2 h
      have : ∃ β ∈ A.letters, β (c y₁) = 0 := by
        by_contra hcon
        simp only [not_exists, not_and] at hcon
        exact hzT ((hY _).2 ⟨hz0, hcon⟩)
      obtain ⟨β, hβ, hβz⟩ := this
      obtain ⟨w₂, hw₂, hw₂0, hlw₂⟩ := (hd (β y₁)).1
      refine ⟨c :: β :: w₂, ⟨(word_cons A).2 ⟨hc, (word_cons A).2 ⟨hβ, hw₂⟩⟩, fun q hq => ?_⟩, ?_⟩
      · rcases (hmemT q).1 hq with rfl | rfl
        · change act w₂ (β (c q)) = 0; rw [hβz]; exact act_zero A w₂ hw₂
        · change act w₂ (β (c q)) = 0; rw [hcy]; exact hw₂0
      · simp only [List.length_cons]
        have := hdist_le (β y₁) (hno β hβ)
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
variable {n k : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (hk : 2 ≤ k) (hA : A.IsAk k) (hcard : (Y A).card ≤ 2)
    (T : Finset (Fin n)) (hT : T ⊆ Y A) (hsize : T.card = 2) :
    Within A T 4 := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A (by omega) hA
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
  exact two_bad' A hk hA hd (Y A) (mem_Y_iff A) hcard T hT hsize
end SinkReset.Plan
