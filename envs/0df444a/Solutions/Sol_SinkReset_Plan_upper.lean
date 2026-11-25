-- Prove2me | solution 1 for SinkReset.Plan.upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:51.727084+00:00
-- url     : https://prove2.me/submissions/0b8c06c9-c13c-4bf8-9785-2e96a217394f

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
public import Theorems.Thm_SinkReset_Plan_act_zero
public import Theorems.Thm_SinkReset_Plan_within_univ
public import Theorems.Thm_SinkReset_Plan_trap
public import Theorems.Thm_SinkReset_Plan_closed_reduction
public import Theorems.Thm_SinkReset_Plan_f_small
public import Theorems.Thm_SinkReset_Plan_f_split
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
private theorem wins_word' {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, A.IsWord w ∧ ∀ q ∈ S, act w q = 0 := by
  induction h with
  | reset S hS => exact ⟨[], word_nil A, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (word_nil A) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, (word_cons A).2 ⟨ha, hw⟩, fun q hq => ?_⟩
    exact hw0 _ (Finset.mem_image_of_mem _ hq)
private theorem word_take {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.take i) :=
  fun a ha => hw a (List.mem_of_mem_take ha)
private theorem word_drop {n : ℕ} [NeZero n] (A : Automaton n) {w : List (Letter n)} (hw : A.IsWord w) (i : ℕ) : A.IsWord (w.drop i) :=
  fun a ha => hw a (List.mem_of_mem_drop ha)
private theorem word_single {n : ℕ} [NeZero n] (A : Automaton n) {a : Letter n} (ha : a ∈ A.letters) : A.IsWord [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  exact hb ▸ ha
private theorem active_card_le {n : ℕ} [NeZero n] (S : Finset (Fin n)) : (S.erase 0).card ≤ n - 1 := by
  calc (S.erase 0).card ≤ (Finset.univ.erase (0 : Fin n)).card :=
        Finset.card_le_card (Finset.erase_subset_erase _ (Finset.subset_univ _))
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
private theorem active_univ_card {n : ℕ} [NeZero n] : ((Finset.univ : Finset (Fin n)).erase 0).card = n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
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
private theorem classical_bound' {n : ℕ} [NeZero n] (A : Automaton n) {d : Fin n → ℕ} (hd : ∀ q, (∃ w, A.IsWord w ∧ act w q = 0 ∧ w.length = d q) ∧
      ∀ w, A.IsWord w → act w q = 0 → d q ≤ w.length) (S : Finset (Fin n)) :
    ∃ w, A.IsWord w ∧ (∀ q ∈ S, act w q = 0) ∧
      w.length ≤ ∑ j ∈ Finset.range (S.erase 0).card, (n - (j + 1)) := by
  classical
  induction hm : (S.erase 0).card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    rcases (S.erase 0).eq_empty_or_nonempty with h | h
    · refine ⟨[], word_nil A, fun q hq => ?_, by simp⟩
      by_contra hq0
      have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
      rw [h] at this; simp at this
    · obtain ⟨q, hq, w, hw, hw0, hlen⟩ := short_kill' A hd S h
      have hdec := kill_decreases' S q hq (act w) (act_zero A w hw) hw0
      obtain ⟨w', hw', hw'0, hlen'⟩ := ih _ (by omega) (S.image (act w)) rfl
      refine ⟨w ++ w', (word_append A w w').2 ⟨hw, hw'⟩, fun p hp => ?_, ?_⟩
      · rw [act_append]; exact hw'0 _ (Finset.mem_image_of_mem _ hp)
      · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [List.length_append, hm', Finset.sum_range_succ]
        have : ∑ j ∈ Finset.range ((S.image (act w)).erase 0).card, (n - (j + 1)) ≤
            ∑ j ∈ Finset.range m', (n - (j + 1)) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
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
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
private theorem closed_set_of_not_sc' {n : ℕ} [NeZero n] (A : Automaton n)
    (h : ¬ ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R := by
  classical
  simp only [not_forall] at h
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  set R := Finset.univ.filter (fun x => x = 0 ∨ ∃ w, A.IsWord w ∧ act w p = x) with hR
  refine ⟨R, by simp [hR], ?_, ?_, ?_⟩
  · have hsub : ({0, p} : Finset (Fin n)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hR]
      · simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨[], word_nil A, rfl⟩
    calc 2 = ({0, p} : Finset (Fin n)).card := (Finset.card_pair (Ne.symm hp)).symm
      _ ≤ R.card := Finset.card_le_card hsub
  · have hqR : q ∉ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      exact ⟨hq, fun ⟨w, hw, hwq⟩ => hpq ⟨w, hw, hwq⟩⟩
    have : R ⊂ Finset.univ := Finset.ssubset_univ_iff.2 fun h => hqR (h ▸ Finset.mem_univ q)
    simpa using Finset.card_lt_card this
  · intro a ha x hx
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · exact Or.inl (A.sink_fixed a ha)
    · refine Or.inr ⟨w ++ [a], (word_append A w [a]).2 ⟨hw, ?_⟩, ?_⟩
      · intro b hb
        simp only [List.mem_singleton] at hb
        exact hb ▸ ha
      · rw [act_append]; rfl
private theorem f_succ (k n : ℕ) : f k (n + 1) = f k n + (n + k - 1) / k := by
  unfold f
  exact Finset.sum_range_succ _ _
private theorem f_cycle' {k m : ℕ} (hk : 1 ≤ k) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by
  induction m with
  | zero => rw [f_small hk (by omega)]; omega
  | succ m ih =>
    rw [show k + (m + 1) + 1 = (k + m + 1) + 1 by omega, f_succ, ih (by omega),
      Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]
    omega
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
private theorem f_lower_aux {k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ k + 3) :
    n - 1 + (n - 1 - k) ≤ f k n := by
  rcases Nat.lt_or_ge n (k + 2) with h | h
  · rw [f_small (by omega) (by omega)]; omega
  · rcases Nat.lt_or_ge n (k + 3) with h' | h'
    · have : n = k + 1 + 1 := by omega
      subst this
      rw [f_cycle' (m := 1) (by omega) (by omega)]; omega
    · have : n = k + 2 + 1 := by omega
      subst this
      rw [f_cycle' (m := 2) (by omega) (by omega)]; omega
private theorem sc_upper' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (hk : 2 ≤ k) (hA : A.IsAk k)
    (hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q)
    (hn : n ≤ k + 3) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  classical
  obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A (by omega) hA
  obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
  set Y := Finset.univ.filter (fun q : Fin n => q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0) with hYdef
  set Z := Finset.univ.filter (fun q : Fin n => q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0) with hZdef
  have hY : ∀ q, q ∈ Y ↔ q ≠ 0 ∧ ∀ a ∈ A.letters, a q ≠ 0 := fun q => by simp [hYdef]
  have hZ : ∀ q, q ∈ Z ↔ q ≠ 0 ∧ ∃ a ∈ A.letters, a q = 0 := fun q => by simp [hZdef]
  have hfew := (few_bad' A hA hsc Y Z hY hZ).2
  have hf := f_lower_aux hk hn
  have hb : n - 1 ≤ f k n := by omega
  refine greedy' A Y hY (f k n) hb fun T hTne hTY => ?_
  have hTc : T.card ≤ n - 1 - k := (Finset.card_le_card hTY).trans hfew
  have hT1 : 1 ≤ T.card := Finset.card_pos.2 hTne
  rcases Nat.lt_or_ge T.card 2 with h | h
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 (show T.card = 1 by omega)
    obtain ⟨w, hw, hw0, hlw⟩ := (hd y).1
    refine ⟨w, ⟨hw, fun q hq => by rw [Finset.mem_singleton] at hq; rw [hq]; exact hw0⟩, ?_⟩
    have h1 := dist_le_Y hd Y hY y
    have h2 : Y.card ≤ n - 1 - k := hfew
    have h3 : y ≠ 0 := ((hY y).1 (hTY (Finset.mem_singleton_self y))).1
    have h4 : 2 ≤ n := by
      by_contra h5
      have : n = 1 := by have := NeZero.ne n; omega
      subst this
      exact h3 (Subsingleton.elim _ _)
    rw [Finset.card_singleton]
    omega
  · have hY2 : Y.card ≤ 2 := by omega
    have hT2 : T.card = 2 := by
      have := Finset.card_le_card hTY; omega
    obtain ⟨w, hw, hlw⟩ := two_bad' A hk hA hd Y hY hY2 T hTY hT2
    refine ⟨w, hw, ?_⟩
    rw [hT2]
    omega
private theorem upper_ge_two {k : ℕ} (hk : 2 ≤ k) : ∀ N n, n ≤ N → ∀ [NeZero n] (A : Automaton n),
    A.IsAk k → n ≤ k + 3 → ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  intro N
  induction N with
  | zero =>
    intro n hn _ _
    exact absurd (Nat.le_zero.1 hn) (NeZero.ne n)
  | succ N ih =>
    intro n hn _ A hA hnk
    by_cases hsc : ∀ p q : Fin n, p ≠ 0 → q ≠ 0 → ∃ w, A.IsWord w ∧ act w p = q
    · exact sc_upper' A hk hA hsc hnk
    · obtain ⟨R, hz, hcard, hproper, hclosed⟩ := closed_set_of_not_sc' A hsc
      obtain ⟨c, d, hc, hd, hcdn, hdR, B, C, hB, hC, hcomb⟩ :=
        closed_reduction A (by omega) hA R hz hcard hproper hclosed
      obtain ⟨u, hu, hlu⟩ := ih (c + 1) (by omega) B hB (by omega)
      obtain ⟨v, hv, hlv⟩ := ih (d + 1) (by omega) C hC (by omega)
      obtain ⟨w, hw, hlw⟩ := hcomb u v hu hv
      refine ⟨w, hw, ?_⟩
      have := f_split (k := k) (c := c) (d := d) (by omega)
      rw [hcdn] at this
      omega
private theorem f_one_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n - 1), (n - (j + 1)) = f 1 n := by
  have hf : f 1 n = ∑ i ∈ Finset.range n, i := by
    unfold f
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hf]
  rcases n with _ | p
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ', add_zero]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    omega
private theorem upper' {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    ∃ w, A.IsReset w ∧ w.length ≤ f k n := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨w₀, hw₀, hw₀0⟩ := wins_word' A le_rfl hA
    obtain ⟨d, hd⟩ := dist_exists A fun q => ⟨w₀, hw₀, hw₀0 q (Finset.mem_univ q)⟩
    obtain ⟨w, hw, hw0, hlw⟩ := classical_bound' A hd Finset.univ
    refine ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, ?_⟩
    rw [active_univ_card, f_one_sum] at hlw
    exact hlw
  · have hnk' : n ≤ k + 3 := by omega
    exact upper_ge_two h n n le_rfl A hA hnk'
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
theorem _root_.solution (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    Within A Finset.univ (f k n) :=
  (within_univ A _).2 (upper' A hk hnk hA)
end SinkReset.Plan
