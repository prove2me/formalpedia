-- Prove2me | solution 1 for SyncPrefix.Huffman.wielandt_code
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:59:20.263063+00:00
-- url     : https://prove2.me/submissions/288fea55-cb53-4887-8255-59496c55a64a

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

open SyncPrefix.Huffman Computability

/-- The counter automaton of `Z_L*`: state `r` = number of letters still missing in the current
codeword. -/
def wStep (L : ℕ) (r : ℕ) (b : Bool) : ℕ := if r = 0 then (if b then L else L - 1) else r - 1

/-- Length of the tail of a codeword starting with `c`. -/
def wLen (L : ℕ) (c : Bool) : ℕ := if c then L else L - 1

lemma wStep_zero (L : ℕ) (c : Bool) : wStep L 0 c = wLen L c := by simp [wStep, wLen]

lemma w_run_cons (L r : ℕ) (c : Bool) (x : List Bool) :
    run (wStep L) r (c :: x) = run (wStep L) (wStep L r c) x := rfl

lemma w_run_append (L r : ℕ) (u v : List Bool) :
    run (wStep L) r (u ++ v) = run (wStep L) (run (wStep L) r u) v := List.foldl_append

lemma w_run_gen (L : ℕ) : ∀ (x : List Bool) (r : ℕ),
    run (wStep L) r x = if r ≤ x.length then run (wStep L) 0 (x.drop r) else r - x.length := by
  intro x
  induction x with
  | nil =>
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [run]
    · simp [run] <;> omega
  | cons c x ih =>
    intro r
    cases r with
    | zero => simp
    | succ r =>
      rw [w_run_cons]
      have : wStep L (r + 1) c = r := by simp [wStep]
      rw [this, ih r]
      simp only [List.length_cons, List.drop_succ_cons]
      by_cases h : r ≤ x.length
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; omega

lemma w_run_le (L : ℕ) : ∀ (x : List Bool) (r : ℕ), r ≤ L → run (wStep L) r x ≤ L := by
  intro x
  induction x with
  | nil => intro r h; exact h
  | cons c x ih =>
    intro r h
    rw [w_run_cons]
    apply ih
    unfold wStep
    split_ifs <;> omega

lemma w_ofFn (n : ℕ) (t : List Bool) : (∃ v : Fin n → Bool, List.ofFn v = t) ↔ t.length = n := by
  constructor
  · rintro ⟨v, rfl⟩; simp
  · intro h
    subst h
    exact ⟨t.get, List.ofFn_get t⟩

lemma w_mem (L : ℕ) (z : List Bool) :
    z ∈ wielandtCode L ↔ ∃ c t, z = c :: t ∧ t.length = wLen L c := by
  simp only [wielandtCode, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨false, _, rfl, by simp [wLen]⟩
    · exact ⟨true, _, rfl, by simp [wLen]⟩
  · rintro ⟨c, t, rfl, ht⟩
    cases c
    · left
      obtain ⟨v, hv⟩ := (w_ofFn (L - 1) t).2 (by simpa [wLen] using ht)
      exact ⟨v, by rw [hv]⟩
    · right
      obtain ⟨v, hv⟩ := (w_ofFn L t).2 (by simpa [wLen] using ht)
      exact ⟨v, by rw [hv]⟩

lemma w_star (L : ℕ) : ∀ v : List Bool,
    v ∈ (lang (wielandtCode L))∗ ↔ run (wStep L) 0 v = 0 := by
  intro v
  induction h : v.length using Nat.strong_induction_on generalizing v with
  | _ n ih =>
  cases v with
  | nil => simp only [run, List.foldl_nil, iff_true]; exact Language.nil_mem_kstar _
  | cons c v' =>
    rw [w_run_cons, wStep_zero, w_run_gen]
    constructor
    · intro hv
      obtain ⟨S, hS, hSmem⟩ := Language.mem_kstar.1 hv
      cases S with
      | nil => simp at hS
      | cons z S' =>
        obtain ⟨c', t, rfl, ht⟩ := (w_mem L z).1 (hSmem _ (List.mem_cons_self ..))
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, hv'⟩ := hS
        have hlen : wLen L c ≤ v'.length := by rw [hv']; simp [ht]
        rw [if_pos hlen]
        have hdrop : v'.drop (wLen L c) = S'.flatten := by
          rw [hv', ← ht, List.drop_left]
        rw [hdrop]
        have hS' : S'.flatten ∈ (lang (wielandtCode L))∗ :=
          Language.mem_kstar.2 ⟨S', rfl, fun y hy => hSmem y (List.mem_cons_of_mem _ hy)⟩
        have hl : S'.flatten.length < n := by
          rw [← h, hv']; simp
        exact (ih _ hl _ rfl).1 hS'
    · intro hrun
      by_cases hlen : wLen L c ≤ v'.length
      · rw [if_pos hlen] at hrun
        have hl : (v'.drop (wLen L c)).length < n := by rw [← h]; simp <;> omega
        have hd := (ih _ hl _ rfl).2 hrun
        obtain ⟨S', hS', hS'mem⟩ := Language.mem_kstar.1 hd
        refine Language.mem_kstar.2 ⟨(c :: v'.take (wLen L c)) :: S', ?_, ?_⟩
        · simp only [List.flatten_cons, List.cons_append, ← hS', List.take_append_drop]
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact (w_mem L _).2 ⟨c, _, rfl, by simp; omega⟩
          · exact hS'mem y hy
      · rw [if_neg hlen] at hrun; omega

lemma w_reach (L : ℕ) (hL : 1 ≤ L) (r : ℕ) (hr : r ≤ L) :
    ∃ u : List Bool, run (wStep L) 0 u = r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · exact ⟨[], rfl⟩
  · refine ⟨true :: List.replicate (L - r) false, ?_⟩
    rw [w_run_cons, wStep_zero, w_run_gen]
    simp only [wLen, if_true, List.length_replicate]
    rw [if_neg (by omega)]
    omega

/-- Words read from `0` back to `0` have length `kL + b` with `b ≤ k`. -/
lemma w_semigroup (L : ℕ) (hL : 1 ≤ L) : ∀ x : List Bool, run (wStep L) 0 x = 0 →
    ∃ k b, b ≤ k ∧ x.length = k * L + b := by
  intro x
  induction h : x.length using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  intro hx
  cases x with
  | nil => exact ⟨0, 0, le_refl _, by simp at h; omega⟩
  | cons c x' =>
    rw [w_run_cons, wStep_zero, w_run_gen] at hx
    by_cases hlen : wLen L c ≤ x'.length
    · rw [if_pos hlen] at hx
      have hl : (x'.drop (wLen L c)).length < n := by rw [← h]; simp <;> omega
      obtain ⟨k, b, hb, hk⟩ := ih _ hl _ rfl hx
      simp only [List.length_drop] at hk
      simp only [List.length_cons] at h
      cases c
      · refine ⟨k + 1, b, by omega, ?_⟩
        simp only [wLen] at hk hlen
        rw [← h]; simp only [Bool.false_eq_true, if_false] at hk hlen
        have : x'.length = k * L + b + (L - 1) := by omega
        rw [this]; ring_nf; omega
      · refine ⟨k + 1, b + 1, by omega, ?_⟩
        simp only [wLen, if_true] at hk hlen
        rw [← h]
        have : x'.length = k * L + b + L := by omega
        rw [this]; ring
    · rw [if_neg hlen] at hx; omega

lemma w_arith (L T : ℕ) (hL : 1 ≤ L)
    (h : ∀ r ≤ L, r ≤ T ∧ ∃ k b, b ≤ k ∧ T - r = k * L + b) : L * L ≤ T := by
  by_contra hT
  push_neg at hT
  have hTL := (h L le_rfl).1
  have hdm := Nat.div_add_mod T L
  have hs := Nat.mod_lt T (by omega : 0 < L)
  set q := T / L
  set s := T % L
  have hq1 : 1 ≤ q := by
    by_contra hq; push_neg at hq
    have : q = 0 := Nat.lt_one_iff.1 hq
    rw [this] at hdm; omega
  have hqL : q < L := by
    by_contra hq; push_neg at hq
    have : L * L ≤ L * q := Nat.mul_le_mul_left _ hq
    omega
  obtain ⟨_, k, b, hbk, hkb⟩ := h (s + 1) (by omega)
  have h1 : k * L + (b + 1) = q * L := by
    have : L * q = q * L := Nat.mul_comm _ _
    omega
  have hkq : k < q := by
    by_contra hk; push_neg at hk
    have : q * L ≤ k * L := Nat.mul_le_mul_right _ hk
    omega
  have hbL : b + 1 < L := by omega
  have := congrArg (· % L) h1
  simp only [Nat.mul_mod_left] at this
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hbL] at this
  omega

/-- The explicit synchronizing word: letter `t` is `1` unless `L ∣ t`. -/
def wWord (L : ℕ) : List Bool := (List.range (L ^ 2)).map fun t => decide (t % L ≠ 0)

lemma wWord_len (L : ℕ) : (wWord L).length = L ^ 2 := by simp [wWord]

lemma wWord_drop (L t : ℕ) (ht : t < L ^ 2) :
    (wWord L).drop t = decide (t % L ≠ 0) :: (wWord L).drop (t + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [wWord_len]; exact ht)]
  simp [wWord]

lemma wWord_A (L : ℕ) (hL : 1 ≤ L) : ∀ j k, k + j = L →
    run (wStep L) 0 ((wWord L).drop (k * L)) = 0 := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have : (wWord L).drop (k * L) = [] := by
      apply List.drop_eq_nil_of_le; rw [wWord_len]; simp at hk; rw [hk]; nlinarith
    rw [this]; rfl
  | succ j ih =>
    intro k hk
    have hkL : k * L + L ≤ L ^ 2 := by
      have : k + 1 ≤ L := by omega
      nlinarith
    rw [wWord_drop L (k * L) (by omega)]
    have hd : decide (k * L % L ≠ 0) = false := by simp [Nat.mul_mod_left]
    rw [hd, w_run_cons, wStep_zero, w_run_gen]
    simp only [wLen, Bool.false_eq_true, if_false, List.length_drop, wWord_len, List.drop_drop]
    rw [if_pos (by omega)]
    have : k * L + 1 + (L - 1) = (k + 1) * L := by
      rw [Nat.add_mul, one_mul]; omega
    rw [this]
    exact ih (k + 1) (by omega)

lemma wWord_Bstep (L : ℕ) (hL : 1 ≤ L) (q s : ℕ) (h1 : 1 ≤ s) (hsL : s < L) (hq : q < s) :
    run (wStep L) 0 ((wWord L).drop (q * L + s)) =
      run (wStep L) 0 ((wWord L).drop (q * L + s + 1 + L)) := by
  have hbound : q * L + s + 1 + L ≤ L ^ 2 := by
    have : (q + 1) * L + L ≤ L * L := by
      have : q + 2 ≤ L := by omega
      nlinarith
    rw [sq]; nlinarith
  rw [wWord_drop L (q * L + s) (by omega)]
  have hd : decide ((q * L + s) % L ≠ 0) = true := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hsL]; simp; omega
  rw [hd, w_run_cons, wStep_zero, w_run_gen]
  simp only [wLen, if_true, List.length_drop, wWord_len, List.drop_drop]
  rw [if_pos (by omega)]

lemma wWord_B (L : ℕ) (hL : 1 ≤ L) : ∀ j q s, s + j = L - 1 → 1 ≤ s → q < s →
    run (wStep L) 0 ((wWord L).drop (q * L + s)) = 0 := by
  intro j
  induction j with
  | zero =>
    intro q s hs h1 hq
    rw [wWord_Bstep L hL q s h1 (by omega) hq]
    have : q * L + s + 1 + L = (q + 2) * L := by
      rw [Nat.add_mul]; omega
    rw [this]
    exact wWord_A L hL (L - (q + 2)) (q + 2) (by omega)
  | succ j ih =>
    intro q s hs h1 hq
    rw [wWord_Bstep L hL q s h1 (by omega) hq]
    have : q * L + s + 1 + L = (q + 1) * L + (s + 1) := by
      rw [Nat.add_mul, one_mul]; omega
    rw [this]
    exact ih (q + 1) (s + 1) (by omega) (by omega) (by omega)

lemma wWord_sync (L : ℕ) (hL : 1 ≤ L) (r : ℕ) (hr : r ≤ L) :
    run (wStep L) r (wWord L) = 0 := by
  rw [w_run_gen, wWord_len]
  have hLL : L ≤ L ^ 2 := by nlinarith
  rw [if_pos (by omega)]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simpa using wWord_A L hL L 0 (by omega)
  · by_cases hrL : r = L
    · rw [hrL]
      simpa using wWord_A L hL (L - 1) 1 (by omega)
    · simpa using wWord_B L hL (L - 1 - r) 0 r (by omega) hr0 hr0

theorem solution (L : ℕ) (hL : 1 ≤ L) :
    IsMaximalPrefixCode (lang (wielandtCode L)) ∧
      (wielandtCode L).card = 3 * 2 ^ (L - 1) ∧
      IsLeast ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) L ∧
      IsGreatest ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) (L + 1) ∧
      (∃ w : List Bool, w.length ≤ L ^ 2 ∧ ∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) ∧
      ∀ w : List Bool, (∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) →
        L ^ 2 - L + 1 ≤ w.length := by
  have hmemL : ∀ z, z ∈ lang (wielandtCode L) ↔ ∃ c t, z = c :: t ∧ t.length = wLen L c :=
    fun z => w_mem L z
  have hlen : ∀ z ∈ wielandtCode L, L ≤ z.length ∧ z.length ≤ L + 1 := by
    intro z hz
    obtain ⟨c, t, rfl, ht⟩ := (w_mem L z).1 hz
    cases c <;> simp [wLen] at ht <;> simp [ht] <;> omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨c, t, h1, _⟩ := (hmemL []).1 h
    simp at h1
  · intro x hx y hy hxy
    obtain ⟨c, t, rfl, ht⟩ := (hmemL x).1 hx
    obtain ⟨c', t', rfl, ht'⟩ := (hmemL y).1 hy
    have hc : c = c' := by
      obtain ⟨s, hs⟩ := hxy
      simp only [List.cons_append, List.cons.injEq] at hs
      exact hs.1
    subst hc
    have := hxy.eq_of_length (by simp [ht, ht'])
    exact this
  · intro X' hX' hle
    apply le_antisymm _ hle
    intro x hx
    have hxne : x ≠ [] := fun h => hX'.1 (h ▸ hx)
    obtain ⟨c, t, rfl⟩ : ∃ c t, x = c :: t := by
      cases x with
      | nil => exact absurd rfl hxne
      | cons c t => exact ⟨c, t, rfl⟩
    by_cases htl : wLen L c ≤ t.length
    · have hz : c :: t.take (wLen L c) ∈ lang (wielandtCode L) :=
        (hmemL _).2 ⟨c, _, rfl, by simp; omega⟩
      have hpre : c :: t.take (wLen L c) <+: c :: t := by
        simp only [List.cons_prefix_cons, true_and]
        exact List.take_prefix _ _
      have := hX'.2 _ (hle hz) _ hx hpre
      rw [← this]; exact hz
    · exfalso
      have hz : c :: (t ++ List.replicate (wLen L c - t.length) false) ∈
          lang (wielandtCode L) := (hmemL _).2 ⟨c, _, rfl, by simp; omega⟩
      have hpre : c :: t <+: c :: (t ++ List.replicate (wLen L c - t.length) false) := by
        simp only [List.cons_prefix_cons, true_and]
        exact List.prefix_append _ _
      have := hX'.2 _ hx _ (hle hz) hpre
      have hl := congrArg List.length this
      simp at hl; omega
  · -- cardinality
    have hdisj : Disjoint
        (Finset.univ.image fun v : Fin (L - 1) → Bool => false :: List.ofFn v)
        (Finset.univ.image fun v : Fin L → Bool => true :: List.ofFn v) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz1 hz2
      obtain ⟨v, rfl⟩ := hz1
      obtain ⟨v', hv'⟩ := hz2
      simp at hv'
    unfold wielandtCode
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective,
      Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have : 2 ^ L = 2 * 2 ^ (L - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    · intro v v' h
      simp only [List.cons.injEq, true_and] at h
      exact List.ofFn_injective h
    · intro v v' h
      simp only [List.cons.injEq, true_and] at h
      exact List.ofFn_injective h
  · refine ⟨false :: List.replicate (L - 1) false, ?_, by simp; omega⟩
    exact (w_mem L _).2 ⟨false, _, rfl, by simp [wLen]⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hlen z hz).1
  · refine ⟨true :: List.replicate L false, ?_, by simp⟩
    exact (w_mem L _).2 ⟨true, _, rfl, by simp [wLen]⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hlen z hz).2
  · refine ⟨wWord L, by rw [wWord_len], fun u => ?_⟩
    rw [w_star, w_run_append]
    exact wWord_sync L hL _ (w_run_le L u 0 (Nat.zero_le _))
  · intro w hw
    have hr : ∀ r ≤ L, r ≤ w.length ∧ ∃ k b, b ≤ k ∧ w.length - r = k * L + b := by
      intro r hrL
      obtain ⟨u, hu⟩ := w_reach L hL r hrL
      have := (w_star L (u ++ w)).1 (hw u)
      rw [w_run_append, hu, w_run_gen] at this
      by_cases hrw : r ≤ w.length
      · rw [if_pos hrw] at this
        obtain ⟨k, b, hb, hk⟩ := w_semigroup L hL _ this
        exact ⟨hrw, k, b, hb, by simpa using hk⟩
      · rw [if_neg hrw] at this; omega
    have := w_arith L w.length hL hr
    have h2 : L ≤ L ^ 2 := by nlinarith
    rw [sq] at h2 ⊢
    omega
