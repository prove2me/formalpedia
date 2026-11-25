-- Prove2me | solution 1 for SinkReset.Plan.lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:14.422504+00:00
-- url     : https://prove2.me/submissions/20fdb942-bc41-46e1-96ca-99ac288c9d03

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append
public import Theorems.Thm_SinkReset_Plan_act_zero
public import Theorems.Thm_SinkReset_Plan_one_game_iff
public import Theorems.Thm_SinkReset_Plan_f_small
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem image_active_le' {n : ℕ} [NeZero n] (S : Finset (Fin n)) (g : Fin n → Fin n) (hg : g 0 = 0) :
    ((S.image g).erase 0).card ≤ (S.erase 0).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S.erase 0) (f := g))
  intro x hx
  obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
  refine Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨fun h => hx0 (h ▸ hg), hp⟩, rfl⟩
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
private theorem act_nil (q : Fin n) : act ([] : List (Letter n)) q = q := rfl
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem wins_of_rank' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S : Finset (Fin n), (S.erase 0).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k → rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S := by
  intro S
  induction hr : rank S using Nat.strong_induction_on generalizing S with
  | _ r ih =>
    rcases (S.erase 0).eq_empty_or_nonempty with h | h
    · refine .reset S fun q hq => ?_
      by_contra hq0
      have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
      rw [h] at this; simp at this
    · obtain ⟨a, ha, hlt⟩ := hstep S h
      exact .step S a ha fun u hu hlen => ih _ (hr ▸ hlt u hu hlen) _ rfl
private theorem word_single {n : ℕ} [NeZero n] (A : Automaton n) {a : Letter n} (ha : a ∈ A.letters) : A.IsWord [a] := by
  intro b hb
  simp only [List.mem_singleton] at hb
  exact hb ▸ ha
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
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
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
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
private theorem potential_bound' {n : ℕ} [NeZero n] (A : Automaton n) (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image a, weight q + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    ∑ q, weight q ≤ w.length := by
  classical
  have key : ∀ (w : List (Letter n)), A.IsWord w → ∀ S : Finset (Fin n),
      ∑ q ∈ S, weight q ≤ ∑ q ∈ S.image (act w), weight q + w.length := by
    intro w
    induction w with
    | nil =>
      intro _ S
      have : S.image (act ([] : List (Letter n))) = S := by ext; simp [act_nil]
      rw [this]; simp
    | cons a w ih =>
      intro hw S
      rw [word_cons] at hw
      have h1 := hstep a hw.1 S
      have h2 := ih hw.2 (S.image a)
      rw [Finset.image_image] at h2
      have : (act w ∘ a) = act (a :: w) := rfl
      rw [this] at h2
      simp only [List.length_cons]
      omega
  have := key w hw.1 Finset.univ
  have h0 : ∑ q ∈ Finset.univ.image (act w), weight q = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hx
    rw [hw.2 q, hzero]
  omega
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
private theorem cyc_token {N : ℕ} [NeZero N] (A : Automaton N) (e : Letter N)
    (hlet : ∀ a ∈ A.letters, a = e ∨ ∀ q, a q = q ∨ a q = 0) :
    ∀ u : List (Letter N), A.IsWord u → ∀ q, act u q ≠ 0 → ∃ r ≤ u.length, act u q = e^[r] q := by
  intro u
  induction u with
  | nil => intro _ q _; exact ⟨0, le_rfl, rfl⟩
  | cons a u ih =>
    intro hu q hne
    rw [word_cons] at hu
    change act u (a q) ≠ 0 at hne
    change ∃ r ≤ u.length + 1, act u (a q) = e^[r] q
    rcases hlet a hu.1 with rfl | h
    · obtain ⟨r, hr, hrq⟩ := ih hu.2 (a q) hne
      exact ⟨r + 1, by omega, by rw [hrq, Function.iterate_succ_apply]⟩
    · rcases h q with h | h
      · rw [h] at hne ⊢
        obtain ⟨r, hr, hrq⟩ := ih hu.2 q hne
        exact ⟨r, by omega, hrq⟩
      · rw [h, act_zero A u hu.2] at hne
        exact absurd rfl hne
private theorem cyc_delta_lt {k m v s : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (δ : ℕ → ℕ)
    (hδ : ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0)
    (hv : v = 1 ∨ (k + 2 ≤ v ∧ v ≤ k + m)) (hs1 : 1 ≤ s) (hsk : s ≤ k) :
    δ ((v - 1 + s) % (k + m) + 1) < δ v := by
  rcases Nat.lt_or_ge (v - 1 + s) (k + m) with h | h
  · rw [Nat.mod_eq_of_lt h, hδ, hδ]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega), hδ, hδ]
    split_ifs <;> omega
private theorem path_exists {n : ℕ} [NeZero n] (k : ℕ) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → n - 1 ≤ w.length := by
  classical
  let pred : Letter n := fun q => ⟨q.val - 1, by omega⟩
  have hpred : ∀ q, (pred q).val = q.val - 1 := fun q => rfl
  let P : Automaton n :=
    { letters := {pred}
      sink_fixed := by
        rintro a rfl
        exact Fin.ext (by rw [hpred]; simp) }
  have hact : ∀ w, P.IsWord w → ∀ q : Fin n, (act w q).val = q.val - w.length := by
    intro w
    induction w with
    | nil => intro _ q; simp [act_nil]
    | cons a w ih =>
      intro hw q
      rw [word_cons] at hw
      have ha : a = pred := hw.1
      change (act w (a q)).val = _
      rw [ih hw.2, ha, hpred, List.length_cons]
      omega
  refine ⟨P, ?_, ?_⟩
  · refine wins_of_rank' P (fun S => ∑ q ∈ S, q.val) (fun S hS => ?_) Finset.univ
    refine ⟨pred, rfl, fun u hu hlen => ?_⟩
    have hu' : P.IsWord (pred :: u) := (word_cons P).2 ⟨rfl, hu⟩
    obtain ⟨q₀, hq₀⟩ := hS
    calc ∑ x ∈ S.image (act (pred :: u)), x.val ≤ ∑ q ∈ S, (act (pred :: u) q).val :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ < ∑ q ∈ S, q.val := by
          refine Finset.sum_lt_sum (fun q _ => by rw [hact _ hu']; omega) ⟨q₀, (Finset.mem_erase.1 hq₀).2, ?_⟩
          rw [hact _ hu']
          have : q₀.val ≠ 0 := fun h => (Finset.mem_erase.1 hq₀).1 (Fin.ext (by simpa using h))
          simp only [List.length_cons]
          omega
  · rintro w ⟨hw, hw0⟩
    have := hact w hw ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [hw0] at this
    simp at this
    omega
private theorem transposition_exists {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ A : Automaton n, A.IsAk 1 ∧ ∀ w, A.IsReset w → f 1 n ≤ w.length := by
  classical
  let kill1 : Letter n := fun q => if q.val = 1 then 0 else q
  let T : Automaton n :=
    { letters := {a | a = kill1 ∨ ∃ i j : Fin n, 1 ≤ i.val ∧ j.val = i.val + 1 ∧
        a = ⇑(Equiv.swap i j)}
      sink_fixed := by
        rintro a (rfl | ⟨i, j, hi, hj, rfl⟩)
        · simp [kill1]
        · refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
          · intro h; rw [← h] at hi; simp at hi
          · intro h; rw [← h] at hj; simp at hj }
  have hkill1 : kill1 ∈ T.letters := Or.inl rfl
  refine ⟨T, ?_, ?_⟩
  · -- every state can be sent to the sink, hence `T` is synchronizing
    have hreach : ∀ v, ∀ q : Fin n, q.val = v → ∃ w, T.IsWord w ∧ act w q = 0 := by
      intro v
      induction v with
      | zero => intro q hq; exact ⟨[], word_nil T, by rw [act_nil]; exact Fin.ext (by simp [hq])⟩
      | succ v ih =>
        intro q hq
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · exact ⟨[kill1], word_single T hkill1, by
            change kill1 q = 0; simp [kill1, hq]⟩
        · let i : Fin n := ⟨v, by omega⟩
          have hsw : ⇑(Equiv.swap i q) ∈ T.letters := Or.inr ⟨i, q, hv, hq, rfl⟩
          obtain ⟨w, hw, hw0⟩ := ih i rfl
          refine ⟨⇑(Equiv.swap i q) :: w, (word_cons T).2 ⟨hsw, hw⟩, ?_⟩
          change act w (Equiv.swap i q q) = 0
          rw [Equiv.swap_apply_right]; exact hw0
    obtain ⟨d, hd⟩ := dist_exists T fun q => hreach q.val q rfl
    obtain ⟨w, hw, hw0, _⟩ := classical_bound' T hd Finset.univ
    exact (one_game_iff T).2 ⟨w, hw, fun q => hw0 q (Finset.mem_univ q)⟩
  · intro w hw
    have hpot := potential_bound' T (fun q => q.val) rfl (fun a ha S => ?_) w hw
    · have hsum : ∑ q : Fin n, q.val = f 1 n := by
        rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
        unfold f
        refine Finset.sum_congr rfl fun i _ => ?_
        simp
      rw [hsum] at hpot
      exact hpot
    · rcases ha with rfl | ⟨i, j, hi, hj, rfl⟩
      · refine pot_kill _ kill1 ⟨1, by omega⟩ (fun q hq => ?_) le_rfl S
        have : q.val ≠ 1 := fun h => hq (Fin.ext h)
        simp [kill1, this]
      · refine pot_perm _ _ (Equiv.injective _) j (fun q hq => ?_) ?_ S
        · by_cases hqi : q = i
          · subst hqi; simp [Equiv.swap_apply_left]; omega
          · simp [Equiv.swap_apply_of_ne_of_ne hqi hq]
        · simp [Equiv.swap_apply_right]; omega
private theorem cycle_exists {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ A : Automaton (k + m + 1), A.IsAk k ∧ ∀ w, A.IsReset w → k + 2 * m ≤ w.length := by
  classical
  have hkm : 0 < k + m := by omega
  let e : Letter (k + m + 1) := fun q =>
    if h : q.val = 0 then 0 else ⟨q.val % (k + m) + 1, by have := Nat.mod_lt q.val hkm; omega⟩
  have he : ∀ q : Fin (k + m + 1), (e q).val = if q.val = 0 then 0 else q.val % (k + m) + 1 := by
    intro q
    by_cases h : q.val = 0
    · rw [if_pos h]
      show (if h : q.val = 0 then (0 : Fin (k + m + 1)) else _).val = 0
      rw [dif_pos h]
      rfl
    · rw [if_neg h]
      show (if h : q.val = 0 then (0 : Fin (k + m + 1)) else _).val = _
      rw [dif_neg h]
  let kl : Fin (k + m + 1) → Letter (k + m + 1) := fun i q => if q = i then 0 else q
  let C : Automaton (k + m + 1) :=
    { letters := {a | a = e ∨ ∃ i : Fin (k + m + 1), 2 ≤ i.val ∧ i.val ≤ k + 1 ∧ a = kl i}
      sink_fixed := by
        rintro a (rfl | ⟨i, _, _, rfl⟩)
        · exact Fin.ext (by rw [he, if_pos (show ((0 : Fin (k + m + 1)) : ℕ) = 0 from rfl)]; rfl)
        · show (if (0 : Fin (k + m + 1)) = i then 0 else 0) = 0
          exact ite_self _ }
  have hval0 : ∀ q : Fin (k + m + 1), q = 0 ↔ q.val = 0 := fun q => Fin.ext_iff
  have hev : ∀ q : Fin (k + m + 1), q.val ≠ 0 →
      (e q).val = if q.val < k + m then q.val + 1 else 1 := by
    intro q hq
    have := q.isLt
    rw [he, if_neg hq]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show q.val = k + m by omega, Nat.mod_self]
  refine ⟨C, ?_, ?_⟩
  · -- `C` is `A_k`: Alice kills a token of `K` if there is one, and plays `e` otherwise
    obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℕ, ∀ v, δ v = if v = 1 then 1 else if k + 1 < v then k + m + 2 - v else 0 :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨delay, hdelay⟩ : ∃ delay : Finset (Fin (k + m + 1)) → ℕ,
        ∀ S, delay S = sInf {r | ∃ q ∈ S.erase 0, δ q.val = r} := ⟨_, fun _ => rfl⟩
    have hδm : ∀ v, δ v ≤ m := fun v => by rw [hδ]; split_ifs <;> omega
    have hdelay_le : ∀ S, delay S ≤ m := by
      intro S
      rw [hdelay]
      rcases (S.erase 0).eq_empty_or_nonempty with h | ⟨q, hq⟩
      · have : {r | ∃ q ∈ S.erase 0, δ q.val = r} = ∅ := by
          ext r; simp [h]
        rw [this, Nat.sInf_empty]; omega
      · exact (Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)).trans (hδm _)
    have hdelay_min : ∀ S, ∀ q ∈ S.erase 0, delay S ≤ δ q.val := fun S q hq => by
      rw [hdelay]; exact Nat.sInf_le (by rw [Set.mem_setOf_eq]; exact ⟨q, hq, rfl⟩)
    have hdelay_mem : ∀ S : Finset (Fin (k + m + 1)), (S.erase 0).Nonempty →
        ∃ q ∈ S.erase 0, δ q.val = delay S := by
      rintro S ⟨q, hq⟩
      rw [hdelay]
      have := Nat.sInf_mem (s := {r | ∃ q ∈ S.erase 0, δ q.val = r}) ⟨_, q, hq, rfl⟩
      rw [Set.mem_setOf_eq] at this
      exact this
    have hlet' : ∀ a ∈ C.letters, a = e ∨ ∀ q, a q = q ∨ a q = 0 := by
      rintro a (rfl | ⟨i, _, _, rfl⟩)
      · exact Or.inl rfl
      · refine Or.inr fun q => ?_
        by_cases h : q = i <;> simp [kl, h]
    refine wins_of_rank' C (fun S => (m + 1) * (S.erase 0).card + delay S) (fun S hS => ?_)
      Finset.univ
    by_cases hK : ∃ i ∈ S.erase 0, 2 ≤ i.val ∧ i.val ≤ k + 1
    · obtain ⟨i, hi, hi2, hik⟩ := hK
      have hkli : kl i ∈ C.letters := Or.inr ⟨i, hi2, hik, rfl⟩
      refine ⟨kl i, hkli, fun u hu _ => ?_⟩
      have hw : C.IsWord (kl i :: u) := (word_cons C).2 ⟨hkli, hu⟩
      have hdec := kill_decreases' S i hi (act (kl i :: u)) (act_zero C _ hw) (by
        change act u (if i = i then 0 else i) = 0
        rw [if_pos rfl]
        exact act_zero C u hu)
      have h1 := hdelay_le (S.image (act (kl i :: u)))
      have h2 := Nat.mul_le_mul_left (m + 1) hdec
      rw [mul_add, mul_one] at h2
      omega
    · simp only [not_exists, not_and] at hK
      refine ⟨e, Or.inl rfl, fun u hu hlen => ?_⟩
      have hw : C.IsWord (e :: u) := (word_cons C).2 ⟨Or.inl rfl, hu⟩
      have hle := image_active_le' S (act (e :: u)) (act_zero C _ hw)
      obtain ⟨q, hq, hqδ⟩ := hdelay_mem S hS
      have hq0 : q.val ≠ 0 := fun h => (Finset.mem_erase.1 hq).1 ((hval0 q).2 h)
      have hqO : q.val = 1 ∨ (k + 2 ≤ q.val ∧ q.val ≤ k + m) := by
        have := q.isLt
        have := hK q hq
        omega
      by_cases hp0 : act (e :: u) q = 0
      · have hdec := kill_decreases' S q hq (act (e :: u)) (act_zero C _ hw) hp0
        have h1 := hdelay_le (S.image (act (e :: u)))
        have h2 := Nat.mul_le_mul_left (m + 1) hdec
        rw [mul_add, mul_one] at h2
        omega
      · obtain ⟨r, hr, hpr⟩ := cyc_token C e hlet' u hu (e q) hp0
        have hp : act (e :: u) q = e^[r + 1] q := by
          change act u (e q) = _
          rw [hpr, Function.iterate_succ_apply]
        have hpval := cyc_iter hkm e he q hq0 (r + 1)
        have hlt := cyc_delta_lt hk hm δ hδ hqO (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ k)
        have hpmem : act (e :: u) q ∈ (S.image (act (e :: u))).erase 0 :=
          Finset.mem_erase.2 ⟨hp0, Finset.mem_image_of_mem _ (Finset.mem_erase.1 hq).2⟩
        have h1 := hdelay_min _ _ hpmem
        rw [hp, hpval] at h1
        have h2 := Nat.mul_le_mul_left (m + 1) hle
        omega
  · -- lower bound by the potential with weight `1` on `K` and `2` on `O`
    intro w hw
    obtain ⟨wt, hwt⟩ : ∃ wt : ℕ → ℕ, ∀ v, wt v = if v = 0 then 0 else if 2 ≤ v ∧ v ≤ k + 1 then 1 else 2 :=
      ⟨_, fun _ => rfl⟩
    have wt0 : wt 0 = 0 := by rw [hwt, if_pos rfl]
    have wt1 : wt 1 = 2 := by rw [hwt]; split_ifs <;> omega
    have wtK : ∀ v, 2 ≤ v → v ≤ k + 1 → wt v = 1 := fun v h1 h2 => by
      rw [hwt]; split_ifs <;> omega
    have wtO : ∀ v, k + 1 < v → wt v = 2 := fun v h1 => by
      rw [hwt]; split_ifs <;> omega
    have wtpos : ∀ v, v ≠ 0 → 1 ≤ wt v := fun v h1 => by
      rw [hwt]; split_ifs <;> omega
    have hpot := potential_bound' C (fun q => wt q.val) wt0 (fun a ha S => ?_) w hw
    · have hsum : ∑ q : Fin (k + m + 1), wt q.val = k + 2 * m := by
        rw [Fin.sum_univ_eq_sum_range wt (k + m + 1)]
        have h1 : ∀ s, s ≤ k → ∑ i ∈ Finset.range (s + 2), wt i = s + 2 := by
          intro s
          induction s with
          | zero =>
            intro _
            rw [Finset.sum_range_succ, Finset.sum_range_one, wt0, wt1]
          | succ s ih =>
            intro hs
            have e1 : ∑ i ∈ Finset.range (s + 1 + 2), wt i =
                ∑ i ∈ Finset.range (s + 2), wt i + wt (s + 2) := Finset.sum_range_succ wt (s + 2)
            rw [e1, ih (by omega), wtK (s + 2) (by omega) (by omega)]
        have h2 : ∀ t, t ≤ m - 1 → ∑ i ∈ Finset.range (k + 2 + t), wt i = k + 2 + 2 * t := by
          intro t
          induction t with
          | zero => intro _; exact h1 k le_rfl
          | succ t ih =>
            intro ht
            have e1 : ∑ i ∈ Finset.range (k + 2 + (t + 1)), wt i =
                ∑ i ∈ Finset.range (k + 2 + t), wt i + wt (k + 2 + t) :=
              Finset.sum_range_succ wt (k + 2 + t)
            rw [e1, ih (by omega), wtO _ (by omega)]
            ring
        rw [show k + m + 1 = k + 2 + (m - 1) by omega, h2 (m - 1) le_rfl]
        omega
      rw [hsum] at hpot
      exact hpot
    · rcases ha with rfl | ⟨i, hi2, hik, rfl⟩
      · let one : Fin (k + m + 1) := ⟨1, by omega⟩
        have hone : one.val = 1 := rfl
        refine pot_perm _ e ?_ one (fun q hq => ?_) ?_ S
        · intro x y hxy
          have h := congrArg Fin.val hxy
          apply Fin.ext
          have hx := x.isLt
          have hy := y.isLt
          by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0
          · omega
          · rw [he x, if_pos hx0, hev y hy0] at h; split_ifs at h <;> omega
          · rw [he y, if_pos hy0, hev x hx0] at h; split_ifs at h <;> omega
          · rw [hev x hx0, hev y hy0] at h; split_ifs at h <;> omega
        · have hq1 : q.val ≠ 1 := fun h => hq (Fin.ext h)
          have := q.isLt
          by_cases hq0 : q.val = 0
          · show wt q.val ≤ wt (e q).val
            rw [hq0, wt0]; exact Nat.zero_le _
          · show wt q.val ≤ wt (e q).val
            have hev' := hev q hq0
            rcases Nat.lt_or_ge (k + 1) q.val with hO | hK'
            · rw [wtO _ hO]
              split_ifs at hev' with hlt
              · rw [hev', wtO _ (by omega)]
              · rw [hev', wt1]
            · rw [wtK _ (by omega) hK']
              exact wtpos _ (by rw [hev']; split_ifs <;> omega)
        · show wt one.val ≤ wt (e one).val + 1
          have h1 := hev one (by rw [hone]; omega)
          rw [hone, if_pos (by omega)] at h1
          rw [h1, hone, wt1, wtK 2 le_rfl (by omega)]
      · refine pot_kill _ (kl i) i (fun q hq => if_neg hq) ?_ S
        show wt i.val ≤ 1
        rw [wtK _ hi2 hik]
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
theorem _root_.solution {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ 2 * k + 1) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by
  rcases Nat.lt_or_ge (k + 1) n with h1 | h1
  · rcases hnk with rfl | hnk
    · exact transposition_exists hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
      obtain ⟨A, hA, hlow⟩ := cycle_exists hk (by omega : 1 ≤ m)
      refine ⟨A, hA, fun w hw => ?_⟩
      rw [f_cycle' hk (by omega)]
      exact hlow w hw
  · obtain ⟨A, hA, hlow⟩ := path_exists (n := n) k
    refine ⟨A, hA, fun w hw => ?_⟩
    rw [f_small hk h1]
    exact hlow w hw
end SinkReset.Plan
