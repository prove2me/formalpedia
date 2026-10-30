-- Prove2me | solution 1 for ZhangJasinPricing.Cyclic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:28:53.990228+00:00
-- url     : https://prove2.me/submissions/e6705613-dceb-4a97-8da5-580dfbebe8d6

import Mathlib
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
open MeasureTheory
open scoped BigOperators ENNReal

namespace S228ZJ
open ZhangJasinPricing.Cyclic

theorem anti {p : ℕ → ℝ} {M : ℕ} (hord : ∀ i j, i < j → j < M → p j < p i) {a b : ℕ}
    (hab : a ≤ b) (hb : b < M) : p b ≤ p a := by
  rcases hab.lt_or_eq with h | h
  · exact (hord a b h hb).le
  · rw [h]

theorem wp_lb {p : ℕ → ℝ} {M : ℕ} (hord : ∀ i j, i < j → j < M → p j < p i) {w : Word}
    {j k : ℕ} (hw : ∀ a ∈ w, a ≤ j) (hj : j < M) (hk : 1 ≤ k) : p j ≤ wordPrice p w k := by
  unfold wordPrice
  rw [if_neg (by omega)]
  apply anti hord _ hj
  cases h : w[k-1]? with
  | none => simp
  | some e => simpa using hw e (List.mem_of_getElem? h)

theorem wp_nonneg {p : ℕ → ℝ} {M : ℕ} (hnn : ∀ i, i < M → 0 ≤ p i) (hM : 0 < M) {w : Word}
    (hw : ∀ a ∈ w, a < M) (k : ℕ) : 0 ≤ wordPrice p w k := by
  unfold wordPrice
  split_ifs
  · exact le_rfl
  · apply hnn
    cases h : w[k-1]? with
    | none => simpa
    | some e => simpa using hw e (List.mem_of_getElem? h)

theorem wp_zero (p : ℕ → ℝ) (w : Word) : wordPrice p w 0 = 0 := by simp [wordPrice]

theorem wp_append_left (p : ℕ → ℝ) {u v : Word} {k : ℕ} (hk : k ≤ u.length) :
    wordPrice p (u ++ v) k = wordPrice p u k := by
  unfold wordPrice
  split_ifs with h
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem wp_append_right (p : ℕ → ℝ) {u v : Word} {m : ℕ} (hm : 1 ≤ m) :
    wordPrice p (u ++ v) (u.length + m) = wordPrice p v m := by
  unfold wordPrice
  rw [if_neg (by omega), if_neg (by omega), List.getElem?_append_right (by omega)]
  congr 3; omega

theorem wp_last (p : ℕ → ℝ) {w : Word} {i : ℕ} (h : w.getLast? = some i) :
    wordPrice p w w.length = p i := by
  have hne : w ≠ [] := by rintro rfl; simp at h
  have hl : 0 < w.length := List.length_pos_of_ne_nil hne
  unfold wordPrice
  rw [if_neg (by omega), ← List.getLast?_eq_getElem?, h]; rfl

theorem sup_cases (S : Finset ℕ) (Pm : ℕ → Prop) (hS : ∀ k, k ∈ S ↔ Pm k) (goal : ℕ → Prop)
    (h0 : goal 0) (h : ∀ T, Pm T → (∀ k, Pm k → k ≤ T) → goal T) : goal (S.sup id) := by
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]; exact h0
  · obtain ⟨T, hT, hTs⟩ := Finset.exists_mem_eq_sup S hne id
    rw [hTs]
    exact h T ((hS T).1 hT) (fun k hk => by
      have := Finset.le_sup (f := id) ((hS k).2 hk); rw [hTs] at this; exact this)

theorem sup_eq (S : Finset ℕ) (Pm : ℕ → Prop) (hS : ∀ k, k ∈ S ↔ Pm k) (T : ℕ) (hT : Pm T)
    (hmax : ∀ k, Pm k → k ≤ T) : S.sup id = T :=
  le_antisymm (Finset.sup_le fun k hk => hmax k ((hS k).1 hk))
    (Finset.le_sup (f := id) ((hS T).2 hT))

theorem crit (p : ℕ → ℝ) (w : Word) (s : ℕ)
    (h : wordPrice p w (s-1) < wordPrice p w s ∨
      (0 ≤ wordPrice p w s ∧ ∀ T, 1 ≤ T → T ≤ s-2 → wordPrice p w T < wordPrice p w (T+1) →
        wordPrice p w T < wordPrice p w (s-1) →
        (∀ k, 1 ≤ k → k ≤ s-2 → wordPrice p w k < wordPrice p w (k+1) →
          wordPrice p w k < wordPrice p w (s-1) → k ≤ T) →
        wordPrice p w T ≤ wordPrice p w s)) :
    wordPrice p w (threshold p w s) ≤ wordPrice p w s := by
  unfold threshold
  split_ifs with h1
  · exact h1.le
  · rcases h with h | ⟨h0, h⟩
    · exact absurd h h1
    · refine sup_cases _ (fun k => 1 ≤ k ∧ k ≤ s-2 ∧ wordPrice p w k < wordPrice p w (k+1) ∧
        wordPrice p w k < wordPrice p w (s-1)) ?_ (fun T => wordPrice p w T ≤ wordPrice p w s)
        ?_ ?_
      · intro k; simp only [Finset.mem_filter, Finset.mem_Icc, and_assoc]
      · simpa [wp_zero] using h0
      · rintro T ⟨a, b, c, d⟩ hm
        exact h T a b c d (fun k a b c d => hm k ⟨a, b, c, d⟩)

theorem extract (p : ℕ → ℝ) (w : Word) (s : ℕ)
    (hn : ¬ wordPrice p w (s-1) < wordPrice p w s)
    (hc : wordPrice p w (threshold p w s) ≤ wordPrice p w s)
    (T : ℕ) (a : 1 ≤ T) (b : T ≤ s-2) (c : wordPrice p w T < wordPrice p w (T+1))
    (d : wordPrice p w T < wordPrice p w (s-1))
    (hm : ∀ k, 1 ≤ k → k ≤ s-2 → wordPrice p w k < wordPrice p w (k+1) →
          wordPrice p w k < wordPrice p w (s-1) → k ≤ T) :
    wordPrice p w T ≤ wordPrice p w s := by
  unfold threshold at hc
  rw [if_neg hn] at hc
  rwa [sup_eq _ (fun k => 1 ≤ k ∧ k ≤ s-2 ∧ wordPrice p w k < wordPrice p w (k+1) ∧
        wordPrice p w k < wordPrice p w (s-1))
      (fun k => by simp only [Finset.mem_filter, Finset.mem_Icc, and_assoc]) T ⟨a, b, c, d⟩
      (fun k ⟨a, b, c, d⟩ => hm k a b c d)] at hc

theorem ascent (q : ℕ → ℝ) : ∀ d a, q a < q (a+d+1) →
    ∃ k, a ≤ k ∧ k ≤ a+d ∧ q k < q (k+1) ∧ q k < q (a+d+1) := by
  intro d
  induction d with
  | zero => intro a h; exact ⟨a, le_rfl, by omega, h, h⟩
  | succ d ih =>
    intro a h
    by_cases h2 : q (a+1) < q (a+(d+1)+1)
    · obtain ⟨k, h1, h3, h4, h5⟩ := ih (a+1) (by rwa [show a+1+d+1 = a+(d+1)+1 by omega])
      exact ⟨k, by omega, by omega, h4, by rwa [show a+1+d+1 = a+(d+1)+1 by omega] at h5⟩
    · exact ⟨a, le_rfl, by omega, lt_of_lt_of_le h (not_lt.1 h2), h⟩

def Inv (p : ℕ → ℝ) (i : ℕ) (w : Word) : Prop :=
  w ≠ [] ∧ (∀ a ∈ w, a ≤ i) ∧ w.getLast? = some i ∧
    ∀ s, 1 ≤ s → s ≤ w.length → wordPrice p w (threshold p w s) ≤ wordPrice p w s

section
variable {p : ℕ → ℝ} {M : ℕ} (hnn : ∀ i, i < M → 0 ≤ p i) (hM : 0 < M)
  (hord : ∀ i j, i < j → j < M → p j < p i)
include hnn hM hord

theorem prefix_cond {u v : Word} (hu : ∀ a ∈ u, a < M) {s : ℕ} (hs : s ≤ u.length)
    (hc : wordPrice p u (threshold p u s) ≤ wordPrice p u s) :
    wordPrice p (u ++ v) (threshold p (u ++ v) s) ≤ wordPrice p (u ++ v) s := by
  have e : ∀ k, k ≤ s → wordPrice p (u ++ v) k = wordPrice p u k :=
    fun k hk => wp_append_left p (by omega)
  apply crit
  by_cases hlt : wordPrice p (u ++ v) (s-1) < wordPrice p (u ++ v) s
  · exact Or.inl hlt
  · right
    refine ⟨by rw [e s le_rfl]; exact wp_nonneg hnn hM hu s, ?_⟩
    intro T a b c d hm
    rw [e s le_rfl, e (s-1) (by omega)] at hlt
    rw [e T (by omega), e (T+1) (by omega)] at c
    rw [e T (by omega), e (s-1) (by omega)] at d
    rw [e T (by omega), e s le_rfl]
    refine extract p u s hlt hc T a b c d (fun k a' b' c' d' => hm k a' b' ?_ ?_)
    · rwa [e k (by omega), e (k+1) (by omega)]
    · rwa [e k (by omega), e (s-1) (by omega)]

theorem inv_single (i : ℕ) (hi : i < M) : Inv p i [i] := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro s h1 h2
  apply crit
  right
  refine ⟨wp_nonneg hnn hM (by simpa using hi) s, ?_⟩
  intro T a b; simp at h2; omega

theorem inv_drop {i j : ℕ} (hi : i < M) (hji : j < i) {y : Word} (hy : Inv p j y) :
    Inv p i (y ++ [i]) := by
  obtain ⟨yne, yle, ylast, ycond⟩ := hy
  have yM : ∀ a ∈ y, a < M := fun a ha => by have := yle a ha; omega
  have wM : ∀ a ∈ y ++ [i], a < M := by
    intro a ha; simp at ha; rcases ha with ha | ha
    · exact yM a ha
    · omega
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro a ha; simp at ha; rcases ha with ha | ha
    · have := yle a ha; omega
    · omega
  intro s h1 h2
  simp only [List.length_append, List.length_singleton] at h2
  rcases Nat.lt_or_ge s (y.length + 1) with hs | hs
  · exact prefix_cond hnn hM hord yM (by omega) (ycond s h1 (by omega))
  · obtain rfl : s = y.length + 1 := by omega
    have yl : 0 < y.length := List.length_pos_of_ne_nil yne
    apply crit
    right
    refine ⟨wp_nonneg hnn hM wM _, ?_⟩
    intro T a b c d hm
    exfalso
    rw [show y.length + 1 - 1 = y.length by omega, wp_append_left p le_rfl, wp_last p ylast,
      wp_append_left p (by omega)] at d
    have := wp_lb hord yle (by omega) a (p := p) (w := y)
    linarith

theorem inv_concat {i : ℕ} (hi : i < M) {u v : Word} (hu : Inv p i u) (hv : Inv p i v) :
    Inv p i (u ++ v) := by
  obtain ⟨une, ule, ulast, ucond⟩ := hu
  obtain ⟨vne, vle, vlast, vcond⟩ := hv
  have uM : ∀ a ∈ u, a < M := fun a ha => by have := ule a ha; omega
  have wle : ∀ a ∈ u ++ v, a ≤ i := by
    intro a ha; simp at ha; rcases ha with ha | ha
    · exact ule a ha
    · exact vle a ha
  have wM : ∀ a ∈ u ++ v, a < M := fun a ha => by have := wle a ha; omega
  refine ⟨by simp [une], wle, by simp [vlast], ?_⟩
  intro s h1 h2
  simp only [List.length_append] at h2
  rcases le_or_gt s u.length with hs | hs
  · exact prefix_cond hnn hM hord uM hs (ucond s h1 hs)
  set n := u.length with hn
  have nl : 0 < n := List.length_pos_of_ne_nil une
  obtain ⟨m, rfl⟩ : ∃ m, s = n + m := ⟨s - n, by omega⟩
  have hm1 : 1 ≤ m := by omega
  set Q := wordPrice p (u ++ v) with hQ
  set q := wordPrice p v with hq
  have eR : ∀ k, 1 ≤ k → Q (n + k) = q k := fun k hk => wp_append_right p hk
  have eN : Q n = p i := by rw [hQ, wp_append_left p le_rfl, wp_last p ulast]
  have lbQ : ∀ k, 1 ≤ k → p i ≤ Q k := fun k hk => wp_lb hord wle hi hk
  have lbq : ∀ k, 1 ≤ k → p i ≤ q k := fun k hk => wp_lb hord vle hi hk
  apply crit
  rw [← hQ]
  by_cases hlt : Q (n + m - 1) < Q (n + m)
  · exact Or.inl hlt
  right
  refine ⟨wp_nonneg hnn hM wM _, ?_⟩
  intro T a b c d hmax
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exfalso
    obtain rfl : m = 1 := by omega
    rw [show n + 1 - 1 = n by omega, eN] at d
    have := lbQ T a; linarith
  have es1 : Q (n + m - 1) = q (m - 1) := by
    rw [show n + m - 1 = n + (m - 1) by omega]; exact eR _ (by omega)
  rcases lt_trichotomy T n with hT | hT | hT
  · exfalso
    have h1 : p i < q (m-1) := by have := lbQ T a; rw [es1] at d; linarith
    by_cases hv1 : p i < q 1
    · have := hmax n nl (by omega) (by rw [eN, eR 1 le_rfl]; exact hv1) (by rw [eN, es1]; exact h1)
      omega
    · have hm3 : 3 ≤ m := by
        by_contra hc
        obtain rfl : m = 2 := by omega
        exact hv1 h1
      obtain ⟨k, k1, k2, k3, k4⟩ := ascent q (m-3) 1
        (by rw [show 1 + (m-3) + 1 = m - 1 by omega]; linarith [not_lt.1 hv1])
      rw [show 1 + (m-3) + 1 = m - 1 by omega] at k4
      have := hmax (n + k) (by omega) (by omega)
        (by rw [eR k k1, show n + k + 1 = n + (k+1) by omega, eR (k+1) (by omega)]; exact k3)
        (by rw [eR k k1, es1]; exact k4)
      omega
  · subst hT; rw [eN, eR m hm1]; exact lbq m hm1
  · obtain ⟨k', rfl⟩ : ∃ k', T = n + k' := ⟨T - n, by omega⟩
    have hk' : 1 ≤ k' := by omega
    rw [eR k' hk', show n + k' + 1 = n + (k'+1) by omega, eR _ (by omega)] at c
    rw [eR k' hk', es1] at d
    rw [eR k' hk', eR m hm1]
    rw [es1, eR m hm1] at hlt
    refine extract p v m hlt (vcond m hm1 (by omega)) k' hk' (by omega) c d ?_
    intro k a' b' c' d'
    have := hmax (n + k) (by omega) (by omega)
      (by rw [eR k a', show n + k + 1 = n + (k+1) by omega, eR (k+1) (by omega)]; exact c')
      (by rw [eR k a', es1]; exact d')
    omega

end

theorem main {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (r : Parameter → ℝ) :
    ∀ fuel t i (x : Plan), i < D.M → x ∈ dp .threshold D.K r fuel t i → Inv D.price i x.1 := by
  have hM : 0 < D.M := by have := D.M_ge; omega
  have hnn := D.price_nonneg
  have hord := D.price_order
  intro fuel
  induction fuel with
  | zero => intro t i x _ hx; simp [dp] at hx
  | succ fuel ih =>
    intro t i x hi hx
    rw [dp] at hx
    split_ifs at hx with h1 h0
    · simp at hx; subst hx; exact inv_single hnn hM hord i hi
    · simp at hx
    · simp only [maximizers, List.mem_filter, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range] at hx
      rcases hx.1 with ⟨k, hk, a, ha, b, hb, rfl⟩ | ⟨j, hj, y, hy, rfl⟩
      · exact inv_concat hnn hM hord hi (ih _ _ _ hi ha) (ih _ _ _ hi hb)
      · exact inv_drop hnn hM hord hi hj (ih _ _ _ (by omega) hy)

end S228ZJ

open ZhangJasinPricing.Cyclic in
theorem solution {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (r : Parameter → ℝ) (t i : ℕ) (ht : 1 ≤ t) (hi : i < D.M)
    (x : Plan) (hx : x ∈ dp .threshold D.K r t t i) :
    ThresholdRegulated D.M D.price x.1 := by
  obtain ⟨hne, hle, hlast, hc⟩ := S228ZJ.main D r t t i x hi hx
  refine ⟨⟨hne, fun a ha => by have := hle a ha; omega⟩, ?_, ?_⟩
  · intro a ha; rw [List.getLastD_eq_getLast?, hlast]; exact hle a ha
  · intro s hs; rw [Finset.mem_Icc] at hs; exact hc s hs.1 hs.2

