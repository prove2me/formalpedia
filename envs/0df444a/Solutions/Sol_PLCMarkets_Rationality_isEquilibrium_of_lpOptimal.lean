-- Prove2me | solution 1 for PLCMarkets.Rationality.isEquilibrium_of_lpOptimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:30:34.961209+00:00
-- url     : https://prove2.me/submissions/9677c44c-ad11-4d62-b136-9630ee32d54a

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

noncomputable def aux_plc_ps : List (ℚ × ℚ) → ℝ → ℝ
  | [], _ => 0
  | (_, a) :: rest, x => min (max x 0) (a : ℝ) + aux_plc_ps rest (x - a)

noncomputable def aux_plc_D (d : ℝ) : List (ℚ × ℚ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | (c, a) :: rest, x, y =>
      ((c : ℝ) - d) * (min (max y 0) (a : ℝ) - min (max x 0) (a : ℝ)) + aux_plc_D d rest (x - a) (y - a)

def aux_plc_Cond (d : ℝ) : List (ℚ × ℚ) → ℝ → Prop
  | [], _ => True
  | (c, a) :: rest, x => (d < (c : ℝ) → (a : ℝ) ≤ x) ∧ ((c : ℝ) < d → x ≤ 0) ∧ aux_plc_Cond d rest (x - a)

noncomputable def aux_plc_F (c : ℝ) (L : List (ℚ × ℚ)) : ℝ :=
  (L.map (fun s => if c < (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

noncomputable def aux_plc_G (c : ℝ) (L : List (ℚ × ℚ)) : ℝ :=
  (L.map (fun s => if c ≤ (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

noncomputable def aux_plc_E (c : ℝ) (L : List (ℚ × ℚ)) : ℝ :=
  (L.map (fun s => if (s.1 : ℝ) = c then (s.2 : ℝ) else 0)).sum

lemma aux_plc_eval_split (d : ℝ) : ∀ (L : List (ℚ × ℚ)) (x y : ℝ),
    plEval L y - plEval L x = d * (aux_plc_ps L y - aux_plc_ps L x) + aux_plc_D d L x y
  | [], x, y => by simp [plEval, aux_plc_ps, aux_plc_D]
  | (c, a) :: rest, x, y => by
    have := aux_plc_eval_split d rest (x - a) (y - a)
    simp only [plEval, aux_plc_ps, aux_plc_D]
    linarith

lemma aux_plc_D_nonpos (d : ℝ) : ∀ (L : List (ℚ × ℚ)) (x y : ℝ),
    aux_plc_Cond d L x → aux_plc_D d L x y ≤ 0
  | [], x, y, _ => by simp [aux_plc_D]
  | (c, a) :: rest, x, y, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have ih := aux_plc_D_nonpos d rest (x - a) (y - a) h3
    simp only [aux_plc_D]
    have : ((c : ℝ) - d) * (min (max y 0) (a : ℝ) - min (max x 0) (a : ℝ)) ≤ 0 := by
      rcases lt_trichotomy (c : ℝ) d with hc | hc | hc
      · have hx := h2 hc
        have : max x 0 = 0 := max_eq_right hx
        rw [this]
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
        have : (0:ℝ) ≤ max y 0 := le_max_right _ _
        have := min_le_min_right (a : ℝ) this
        linarith
      · rw [hc]; simp
      · have hx := h1 hc
        have : min (max x 0) (a : ℝ) = a := min_eq_right (le_trans hx (le_max_left _ _))
        rw [this]
        apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
        have := min_le_right (max y 0) (a : ℝ)
        linarith
    linarith

lemma aux_plc_ps_total : ∀ (L : List (ℚ × ℚ)), (∀ s ∈ L, 0 ≤ s.2) → ∀ x : ℝ,
    aux_plc_ps L x + max (x - (((L.map Prod.snd).sum : ℚ) : ℝ)) 0 = max x 0
  | [], _, x => by simp [aux_plc_ps]
  | (c, a) :: rest, h, x => by
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h (c, a) (by simp)
    have ih := aux_plc_ps_total rest (fun s hs => h s (by simp [hs])) (x - a)
    simp only [aux_plc_ps, List.map_cons, List.sum_cons]
    rw [Rat.cast_add]
    have e : x - (↑a + ↑(List.map Prod.snd rest).sum) = x - ↑a - ↑(List.map Prod.snd rest).sum := by ring
    rw [e]
    have : min (max x 0) (a : ℝ) + max (x - a) 0 = max x 0 := by
      rcases le_total (a : ℝ) x with hax | hax
      · rw [min_eq_right (le_trans hax (le_max_left _ _)), max_eq_left (by linarith),
          max_eq_left (by linarith)]; ring
      · rw [max_eq_right (by linarith : x - (a:ℝ) ≤ 0)]
        rcases le_total x 0 with hx | hx
        · rw [max_eq_right hx]; simp [ha]
        · rw [max_eq_left hx, min_eq_left hax]; ring
    linarith

lemma aux_plc_G_le_total : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, 0 ≤ s.2) →
    aux_plc_G c L ≤ (((L.map Prod.snd).sum : ℚ) : ℝ)
  | _, [], _ => by simp [aux_plc_G]
  | c, (s1, a) :: rest, h => by
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h (s1, a) (by simp)
    have ih := aux_plc_G_le_total c rest (fun s hs => h s (by simp [hs]))
    simp only [aux_plc_G, List.map_cons, List.sum_cons] at ih ⊢
    rw [Rat.cast_add]
    split_ifs <;> linarith

lemma aux_plc_G_eq_total : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, c ≤ (s.1 : ℝ)) →
    aux_plc_G c L = (((L.map Prod.snd).sum : ℚ) : ℝ)
  | _, [], _ => by simp [aux_plc_G]
  | c, (s1, a) :: rest, h => by
    have ih := aux_plc_G_eq_total c rest (fun s hs => h s (by simp [hs]))
    have hc : c ≤ (s1 : ℝ) := h (s1, a) (by simp)
    simp only [aux_plc_G, List.map_cons, List.sum_cons] at ih ⊢
    rw [Rat.cast_add, if_pos hc, ih]

lemma aux_plc_F_nonneg : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, 0 ≤ s.2) → 0 ≤ aux_plc_F c L
  | _, [], _ => by simp [aux_plc_F]
  | c, (s1, a) :: rest, h => by
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h (s1, a) (by simp)
    have ih := aux_plc_F_nonneg c rest (fun s hs => h s (by simp [hs]))
    simp only [aux_plc_F, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> linarith

lemma aux_plc_E_nonneg : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, 0 ≤ s.2) → 0 ≤ aux_plc_E c L
  | _, [], _ => by simp [aux_plc_E]
  | c, (s1, a) :: rest, h => by
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h (s1, a) (by simp)
    have ih := aux_plc_E_nonneg c rest (fun s hs => h s (by simp [hs]))
    simp only [aux_plc_E, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> linarith

lemma aux_plc_G_eq : ∀ (c : ℝ) (L : List (ℚ × ℚ)), aux_plc_G c L = aux_plc_F c L + aux_plc_E c L
  | _, [] => by simp [aux_plc_G, aux_plc_F, aux_plc_E]
  | c, (s1, a) :: rest => by
    have ih := aux_plc_G_eq c rest
    simp only [aux_plc_G, aux_plc_F, aux_plc_E, List.map_cons, List.sum_cons] at ih ⊢
    rcases lt_trichotomy c (s1 : ℝ) with h | h | h
    · rw [if_pos h.le, if_pos h, if_neg h.ne']; linarith
    · rw [if_pos h.le, if_neg (by rw [h]; exact lt_irrefl _), if_pos h.symm]
      linarith
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg h.ne]; linarith

lemma aux_plc_G_zero : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, (s.1 : ℝ) < c) → aux_plc_G c L = 0
  | _, [], _ => by simp [aux_plc_G]
  | c, (s1, a) :: rest, h => by
    have ih := aux_plc_G_zero c rest (fun s hs => h s (by simp [hs]))
    have hc : (s1 : ℝ) < c := h (s1, a) (by simp)
    simp only [aux_plc_G, List.map_cons, List.sum_cons] at ih ⊢
    rw [if_neg (not_le.mpr hc), ih]; simp

lemma aux_plc_F_zero : ∀ (c : ℝ) (L : List (ℚ × ℚ)), (∀ s ∈ L, (s.1 : ℝ) ≤ c) → aux_plc_F c L = 0
  | _, [], _ => by simp [aux_plc_F]
  | c, (s1, a) :: rest, h => by
    have ih := aux_plc_F_zero c rest (fun s hs => h s (by simp [hs]))
    have hc : (s1 : ℝ) ≤ c := h (s1, a) (by simp)
    simp only [aux_plc_F, List.map_cons, List.sum_cons] at ih ⊢
    rw [if_neg (not_lt.mpr hc), ih]; simp

lemma aux_plc_condC (d : ℝ) : ∀ (L : List (ℚ × ℚ)), (∀ s ∈ L, (s.1 : ℝ) = d) → ∀ x, aux_plc_Cond d L x
  | [], _, x => by simp [aux_plc_Cond]
  | (c, a) :: rest, h, x => by
    have hc : (c : ℝ) = d := h (c, a) (by simp)
    refine ⟨fun h' => by rw [hc] at h'; exact absurd h' (lt_irrefl _),
      fun h' => by rw [hc] at h'; exact absurd h' (lt_irrefl _),
      aux_plc_condC d rest (fun s hs => h s (by simp [hs])) _⟩

lemma aux_plc_condA (c' d : ℝ) : ∀ (L : List (ℚ × ℚ)), L.Pairwise (fun s t => t.1 ≤ s.1) →
    (∀ s ∈ L, 0 ≤ s.2) → (∀ s ∈ L, (s.1 : ℝ) ≤ c') →
    (∀ s ∈ L, ((s.1 : ℝ) = c' → (s.1 : ℝ) = d) ∧ ((s.1 : ℝ) < c' → (s.1 : ℝ) ≤ d)) →
    ∀ x, x ≤ aux_plc_G c' L → aux_plc_Cond d L x
  | [], _, _, _, _, x, _ => by simp [aux_plc_Cond]
  | (c, a) :: rest, hpw, hnn, hle, hsl, x, hx => by
    rw [List.pairwise_cons] at hpw
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hnn (c, a) (by simp)
    have hcle : (c : ℝ) ≤ c' := hle (c, a) (by simp)
    have hsl0 := hsl (c, a) (by simp)
    simp only at hsl0
    have hrest : ∀ t ∈ rest, (t.1 : ℝ) ≤ c := fun t ht => by exact_mod_cast hpw.1 t ht
    have ih := aux_plc_condA c' d rest hpw.2 (fun s hs => hnn s (by simp [hs]))
      (fun s hs => hle s (by simp [hs])) (fun s hs => hsl s (by simp [hs]))
    simp only [aux_plc_G, List.map_cons, List.sum_cons] at hx
    rcases hcle.lt_or_eq with hlt | heq
    · have hcd := hsl0.2 hlt
      have hG : aux_plc_G c' rest = 0 :=
        aux_plc_G_zero c' rest (fun t ht => lt_of_le_of_lt (hrest t ht) hlt)
      simp only [aux_plc_G] at hG
      rw [if_neg (not_le.mpr hlt), hG] at hx
      refine ⟨fun h => absurd hcd (not_le.mpr h), fun _ => by linarith, ih _ ?_⟩
      simp only [aux_plc_G]; rw [hG]; linarith
    · have hcd := hsl0.1 heq
      rw [if_pos heq.ge] at hx
      refine ⟨fun h => by rw [hcd] at h; exact absurd h (lt_irrefl _),
        fun h => by rw [hcd] at h; exact absurd h (lt_irrefl _), ih _ ?_⟩
      simp only [aux_plc_G]; linarith

lemma aux_plc_condB (c' d : ℝ) : ∀ (L : List (ℚ × ℚ)), L.Pairwise (fun s t => t.1 ≤ s.1) →
    (∀ s ∈ L, 0 ≤ s.2) →
    (∀ s ∈ L, (c' < (s.1 : ℝ) → d ≤ (s.1 : ℝ)) ∧ ((s.1 : ℝ) = c' → (s.1 : ℝ) = d) ∧
      ((s.1 : ℝ) < c' → (s.1 : ℝ) ≤ d)) →
    ∀ x, aux_plc_F c' L ≤ x → (x ≤ aux_plc_G c' L ∨ ∀ s ∈ L, c' ≤ (s.1 : ℝ)) → aux_plc_Cond d L x
  | [], _, _, _, x, _, _ => by simp [aux_plc_Cond]
  | (c, a) :: rest, hpw, hnn, hsl, x, hF, hG => by
    have hpw' := hpw
    rw [List.pairwise_cons] at hpw'
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hnn (c, a) (by simp)
    have hsl0 := hsl (c, a) (by simp)
    simp only at hsl0
    have hrest : ∀ t ∈ rest, (t.1 : ℝ) ≤ c := fun t ht => by exact_mod_cast hpw'.1 t ht
    rcases lt_or_ge c' (c : ℝ) with hlt | hge
    · have hdc := hsl0.1 hlt
      have ih := aux_plc_condB c' d rest hpw'.2 (fun s hs => hnn s (by simp [hs]))
        (fun s hs => hsl s (by simp [hs]))
      have hFr := aux_plc_F_nonneg c' rest (fun s hs => hnn s (by simp [hs]))
      simp only [aux_plc_F, List.map_cons, List.sum_cons] at hF hFr
      rw [if_pos hlt] at hF
      refine ⟨fun _ => by linarith, fun h => absurd hdc (not_le.mpr h), ih _ ?_ ?_⟩
      · simp only [aux_plc_F]; linarith
      · rcases hG with hG | hG
        · left
          simp only [aux_plc_G, List.map_cons, List.sum_cons] at hG
          rw [if_pos hlt.le] at hG
          simp only [aux_plc_G]; linarith
        · right; exact fun s hs => hG s (by simp [hs])
    · have hall : ∀ s ∈ (c, a) :: rest, (s.1 : ℝ) ≤ c' := by
        intro s hs
        rcases List.mem_cons.mp hs with h | h
        · rw [h]; exact hge
        · exact le_trans (hrest s h) hge
      rcases hG with hG | hG
      · exact aux_plc_condA c' d _ hpw hnn hall (fun s hs => ⟨(hsl s hs).2.1, (hsl s hs).2.2⟩) x hG
      · apply aux_plc_condC
        intro s hs
        exact (hsl s hs).2.1 (le_antisymm (hall s hs) (hG s hs))

lemma aux_plc_nec (d : ℝ) : ∀ (L : List (ℚ × ℚ)), L.Pairwise (fun s t => t.1 ≤ s.1) →
    (∀ s ∈ L, 0 < s.2) → ∀ x y, aux_plc_Cond d L x → 0 ≤ aux_plc_D d L x y →
    aux_plc_F d L ≤ max y 0 ∧ (y ≤ aux_plc_G d L ∨ ∀ s ∈ L, d ≤ (s.1 : ℝ))
  | [], _, _, x, y, _, _ => by simp [aux_plc_F, aux_plc_G]
  | (c, a) :: rest, hpw, hpos, x, y, hC, hD => by
    have hpw' := hpw
    rw [List.pairwise_cons] at hpw'
    have ha : (0 : ℝ) < a := by exact_mod_cast hpos (c, a) (by simp)
    have hrest : ∀ t ∈ rest, (t.1 : ℝ) ≤ c := fun t ht => by exact_mod_cast hpw'.1 t ht
    obtain ⟨h1, h2, h3⟩ := hC
    have hDr := aux_plc_D_nonpos d rest (x - a) (y - a) h3
    have hDcons := aux_plc_D_nonpos d ((c, a) :: rest) x y ⟨h1, h2, h3⟩
    simp only [aux_plc_D] at hD hDcons
    -- the head term
    set t := ((c : ℝ) - d) * (min (max y 0) (a : ℝ) - min (max x 0) (a : ℝ)) with ht
    have htle : t ≤ 0 := by
      have := aux_plc_D_nonpos d [(c, a)] x y ⟨h1, h2, trivial⟩
      simp only [aux_plc_D] at this; linarith
    have ht0 : t = 0 := by linarith
    have hDr0 : 0 ≤ aux_plc_D d rest (x - a) (y - a) := by linarith
    have ih := aux_plc_nec d rest hpw'.2 (fun s hs => hpos s (by simp [hs])) (x - a) (y - a) h3 hDr0
    simp only [aux_plc_F, aux_plc_G, List.map_cons, List.sum_cons] at ih ⊢
    rcases lt_trichotomy d (c : ℝ) with hlt | heq | hgt
    · have hx := h1 hlt
      have hmx : min (max x 0) (a : ℝ) = a := min_eq_right (le_trans hx (le_max_left _ _))
      rw [hmx] at ht
      have hmy : min (max y 0) (a : ℝ) = a := by
        have : ((c : ℝ) - d) ≠ 0 := by linarith
        have := (mul_eq_zero.mp (ht ▸ ht0)).resolve_left this
        linarith
      have hya : (a : ℝ) ≤ y := by
        have h' : (a : ℝ) ≤ max y 0 := by rw [← hmy]; exact min_le_left _ _
        rcases le_total y 0 with hy | hy
        · rw [max_eq_right hy] at h'; linarith
        · rwa [max_eq_left hy] at h'
      rw [if_pos hlt, if_pos hlt.le, max_eq_left (by linarith : (0:ℝ) ≤ y)]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ y - a)] at ih
      refine ⟨by linarith, ?_⟩
      rcases ih.2 with h | h
      · left; linarith
      · right
        intro s hs
        rcases List.mem_cons.mp hs with h' | h'
        · rw [h']; exact hlt.le
        · exact h s h'
    · have hF0 := aux_plc_F_zero d rest (fun t ht => heq ▸ hrest t ht)
      simp only [aux_plc_F] at hF0
      rw [if_neg (by rw [heq]; exact lt_irrefl _), if_pos heq.le, hF0]
      refine ⟨by simp, ?_⟩
      rcases ih.2 with h | h
      · left; linarith
      · right
        intro s hs
        rcases List.mem_cons.mp hs with h' | h'
        · rw [h']; exact heq.le
        · exact h s h'
    · have hx := h2 hgt
      have hmx : min (max x 0) (a : ℝ) = 0 := by rw [max_eq_right hx]; exact min_eq_left ha.le
      rw [hmx] at ht
      have hmy : min (max y 0) (a : ℝ) = 0 := by
        have : ((c : ℝ) - d) ≠ 0 := by linarith
        have := (mul_eq_zero.mp (ht ▸ ht0)).resolve_left this
        linarith
      have hy0 : y ≤ 0 := by
        rcases le_total y 0 with hy | hy
        · exact hy
        · rw [max_eq_left hy] at hmy
          rcases le_total y (a : ℝ) with h' | h'
          · rw [min_eq_left h'] at hmy; linarith
          · rw [min_eq_right h'] at hmy; linarith
      have hF0 := aux_plc_F_zero d rest (fun t ht => le_trans (hrest t ht) hgt.le)
      have hG0 := aux_plc_G_zero d rest (fun t ht => lt_of_le_of_lt (hrest t ht) hgt)
      simp only [aux_plc_F, aux_plc_G] at hF0 hG0
      rw [if_neg (not_lt.mpr hgt.le), if_neg (not_le.mpr hgt), hF0, hG0]
      exact ⟨by simp, Or.inl (by simp; exact hy0)⟩

noncomputable def aux_plc_T (L : List (ℚ × ℚ)) : ℝ := (((L.map Prod.snd).sum : ℚ) : ℝ)

lemma aux_plc_eval_split' (f : PLConcave) (d x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f.eval y - f.eval x = d * (y - x) + (aux_plc_D d f.segs x y +
      ((f.tail : ℝ) - d) * (max (y - aux_plc_T f.segs) 0 - max (x - aux_plc_T f.segs) 0)) := by
  have hnn : ∀ s ∈ f.segs, 0 ≤ s.2 := fun s hs => (f.amount_pos s hs).le
  have e1 := aux_plc_eval_split d f.segs x y
  have e2 := aux_plc_ps_total f.segs hnn x
  have e3 := aux_plc_ps_total f.segs hnn y
  rw [max_eq_left hx] at e2
  rw [max_eq_left hy] at e3
  unfold PLConcave.eval aux_plc_T
  linear_combination e1 + d * e3 - d * e2

lemma aux_plc_sup (f : PLConcave) (c' d x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : ∀ s ∈ f.segs, (c' < (s.1 : ℝ) → d ≤ (s.1 : ℝ)) ∧ ((s.1 : ℝ) = c' → (s.1 : ℝ) = d) ∧
      ((s.1 : ℝ) < c' → (s.1 : ℝ) ≤ d))
    (h2 : (f.tail : ℝ) ≤ c') (h3 : (f.tail : ℝ) = c' → (f.tail : ℝ) = d)
    (h4 : (f.tail : ℝ) < c' → (f.tail : ℝ) ≤ d)
    (hx1 : aux_plc_F c' f.segs ≤ x) (hx2 : (f.tail : ℝ) < c' → x ≤ aux_plc_G c' f.segs) :
    f.eval y - f.eval x ≤ d * (y - x) := by
  have hnn : ∀ s ∈ f.segs, 0 ≤ s.2 := fun s hs => (f.amount_pos s hs).le
  rw [aux_plc_eval_split' f d x y hx hy]
  have hC : aux_plc_Cond d f.segs x := by
    apply aux_plc_condB c' d f.segs f.slope_antitone hnn h1 x hx1
    rcases h2.lt_or_eq with h | h
    · exact Or.inl (hx2 h)
    · right; intro s hs; rw [← h]; exact_mod_cast f.tail_le s hs
  have hD := aux_plc_D_nonpos d f.segs x y hC
  have htail : ((f.tail : ℝ) - d) *
      (max (y - aux_plc_T f.segs) 0 - max (x - aux_plc_T f.segs) 0) ≤ 0 := by
    rcases h2.lt_or_eq with h | h
    · have htd := h4 h
      have hxT : x ≤ aux_plc_T f.segs := le_trans (hx2 h) (aux_plc_G_le_total c' f.segs hnn)
      rw [max_eq_right (by linarith : x - aux_plc_T f.segs ≤ 0)]
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
      have := le_max_right (y - aux_plc_T f.segs) 0
      linarith
    · rw [h3 h]; simp
  linarith

lemma aux_plc_necgood (f : PLConcave) (d x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h2 : (f.tail : ℝ) ≤ d)
    (hx1 : aux_plc_F d f.segs ≤ x) (hx2 : (f.tail : ℝ) < d → x ≤ aux_plc_G d f.segs)
    (hge : d * (y - x) ≤ f.eval y - f.eval x) :
    aux_plc_F d f.segs ≤ y ∧ ((f.tail : ℝ) < d → y ≤ aux_plc_G d f.segs) := by
  have hnn : ∀ s ∈ f.segs, 0 ≤ s.2 := fun s hs => (f.amount_pos s hs).le
  rw [aux_plc_eval_split' f d x y hx hy] at hge
  have hC : aux_plc_Cond d f.segs x := by
    apply aux_plc_condB d d f.segs f.slope_antitone hnn
      (fun s _ => ⟨fun h => h.le, fun h => h, fun h => h.le⟩) x hx1
    rcases h2.lt_or_eq with h | h
    · exact Or.inl (hx2 h)
    · right; intro s hs; rw [← h]; exact_mod_cast f.tail_le s hs
  have hD := aux_plc_D_nonpos d f.segs x y hC
  have htail : ((f.tail : ℝ) - d) *
      (max (y - aux_plc_T f.segs) 0 - max (x - aux_plc_T f.segs) 0) ≤ 0 := by
    rcases h2.lt_or_eq with h | h
    · have hxT : x ≤ aux_plc_T f.segs := le_trans (hx2 h) (aux_plc_G_le_total d f.segs hnn)
      rw [max_eq_right (by linarith : x - aux_plc_T f.segs ≤ 0)]
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
      have := le_max_right (y - aux_plc_T f.segs) 0
      linarith
    · rw [h]; simp
  have hD0 : 0 ≤ aux_plc_D d f.segs x y := by linarith
  have htail0 : ((f.tail : ℝ) - d) *
      (max (y - aux_plc_T f.segs) 0 - max (x - aux_plc_T f.segs) 0) = 0 := by linarith
  obtain ⟨hF, hG⟩ := aux_plc_nec d f.segs f.slope_antitone f.amount_pos x y hC hD0
  rw [max_eq_left hy] at hF
  refine ⟨hF, fun htd => ?_⟩
  rcases hG with hG | hG
  · exact hG
  · have hGT := aux_plc_G_eq_total d f.segs hG
    have hxT : x ≤ aux_plc_T f.segs := le_trans (hx2 htd) (aux_plc_G_le_total d f.segs hnn)
    rw [max_eq_right (by linarith : x - aux_plc_T f.segs ≤ 0)] at htail0
    have hne : ((f.tail : ℝ) - d) ≠ 0 := by linarith
    have hm := (mul_eq_zero.mp htail0).resolve_left hne
    have : y - aux_plc_T f.segs ≤ 0 := by
      have := le_max_left (y - aux_plc_T f.segs) 0
      linarith
    unfold aux_plc_T at this
    rw [hGT]; linarith

namespace FisherMarket

variable {n g : ℕ}

lemma aux_plc_forcedAmount (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (j : Fin g)
    (hp : 0 < p j) :
    M.forcedAmount p i j = aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs := by
  unfold forcedAmount IsForcedSeg segBpb segSlope segAmount aux_plc_F
  rw [Finset.sum_filter, ← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro k _
  simp only [List.get_eq_getElem]
  by_cases h : M.flexBpb p i < (((M.util i j).segs[k.1]).1 : ℝ) / p j
  · rw [if_pos h, if_pos ((lt_div_iff₀ hp).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((lt_div_iff₀ hp).mpr h'))]

lemma aux_plc_flexCapLP (M : FisherMarket n g) (p' q : Fin g → ℝ) (i : Fin n) (j : Fin g)
    (hp : 0 < p' j) :
    M.flexCapLP p' j i q = aux_plc_E (M.flexBpb p' i * p' j) (M.util i j).segs * q j := by
  unfold flexCapLP IsFlexibleSeg segBpb segSlope segAmount aux_plc_E
  rw [Finset.sum_filter, ← Fin.sum_univ_fun_getElem, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [List.get_eq_getElem]
  by_cases h : (((M.util i j).segs[k.1]).1 : ℝ) / p' j = M.flexBpb p' i
  · rw [if_pos h, if_pos ((div_eq_iff hp.ne').mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((div_eq_iff hp.ne').mpr h'))]; simp

lemma aux_plc_spentLP (M : FisherMarket n g) (p' q : Fin g → ℝ) (i : Fin n) :
    M.spentLP p' i q = ∑ j, q j * M.forcedAmount p' i j := by
  unfold spentLP forcedAmount
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

lemma aux_plc_spent (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) :
    M.spent p i = M.spentLP p i p := rfl

lemma aux_plc_vae_sum (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (r : ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => r ≤ M.segBpb p s), M.segValue p s =
      ∑ j, p j * aux_plc_G (r * p j) (M.util i j).segs := by
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  unfold aux_plc_G
  rw [← Fin.sum_univ_fun_getElem, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold segBpb segValue segSlope segAmount
  simp only [List.get_eq_getElem]
  by_cases h : r ≤ (((M.util i j).segs[k.1]).1 : ℝ) / p j
  · rw [if_pos h, if_pos ((le_div_iff₀ (hp j)).mp h)]; ring
  · rw [if_neg h, if_neg (fun h' => h ((le_div_iff₀ (hp j)).mpr h'))]; simp

lemma aux_plc_pieceSlope_nonneg (M : FisherMarket n g) {i : Fin n} (σ : M.Piece i) :
    (0 : ℝ) ≤ (M.pieceSlope σ : ℝ) := by
  obtain ⟨j, o⟩ := σ
  cases o with
  | none => exact_mod_cast (M.util i j).tail_nonneg
  | some k => exact_mod_cast (M.util i j).slope_nonneg _ (List.get_mem _ _)

lemma aux_plc_flex_facts (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (j0 : Fin g) :
    (∃ σ : M.Piece i, M.pieceBpb p σ = M.flexBpb p i) ∧
    M.ValueAboveExceeds p i (M.flexBpb p i) ∧
    (∀ τ : M.Piece i, M.ValueAboveExceeds p i (M.pieceBpb p τ) →
      M.pieceBpb p τ ≤ M.flexBpb p i) := by
  set S := {r | r ∈ Set.range (fun s : M.Piece i => M.pieceBpb p s) ∧
    M.ValueAboveExceeds p i r} with hS
  have hfin : S.Finite := (Set.finite_range _).subset (fun r hr => hr.1)
  have hne : S.Nonempty := ⟨M.pieceBpb p ⟨j0, none⟩, ⟨⟨_, rfl⟩, Or.inl ⟨j0, le_rfl⟩⟩⟩
  have hmem : M.flexBpb p i ∈ S := hne.csSup_mem hfin
  refine ⟨?_, hmem.2, ?_⟩
  · obtain ⟨σ, hσ⟩ := hmem.1; exact ⟨σ, hσ⟩
  · intro τ hτ; exact le_csSup hfin.bddAbove ⟨⟨τ, rfl⟩, hτ⟩

open Classical in
lemma aux_plc_spent_le (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (hle : ∀ τ : M.Piece i, M.ValueAboveExceeds p i (M.pieceBpb p τ) →
      M.pieceBpb p τ ≤ M.flexBpb p i) :
    M.spent p i ≤ M.budget i := by
  unfold spent
  rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun s : M.Seg i => M.IsForcedSeg p s)) with hT | hT
  · rw [hT]; simp only [Finset.sum_empty]; exact_mod_cast (M.budget_pos i).le
  · obtain ⟨s0, hs0, hmin⟩ := Finset.exists_min_image _ (fun s => M.segBpb p s) hT
    have hs0f : M.flexBpb p i < M.segBpb p s0 := (Finset.mem_filter.mp hs0).2
    have hnot : ¬ M.ValueAboveExceeds p i (M.segBpb p s0) := by
      intro hV
      have := hle ⟨s0.1, some s0.2⟩ hV
      have e : M.pieceBpb p ⟨s0.1, some s0.2⟩ = M.segBpb p s0 := rfl
      linarith
    unfold ValueAboveExceeds at hnot
    push Not at hnot
    refine le_trans ?_ hnot.2
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨Finset.mem_univ _, hmin s (Finset.mem_filter.mpr hs)⟩
    · intro s _ _
      unfold segValue segAmount
      apply mul_nonneg _ (hp _).le
      exact_mod_cast ((M.util i s.1).amount_pos _ (List.get_mem _ _)).le

lemma aux_plc_necessity (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (j0 : Fin g) (x : Fin g → ℝ) (hx : M.IsOptimalBundle p i x) (j : Fin g) :
    M.forcedAmount p i j ≤ x j ∧ (¬ M.IsFlexibleTail p i j →
      x j ≤ M.forcedAmount p i j + aux_plc_E (M.flexBpb p i * p j) (M.util i j).segs) := by
  obtain ⟨⟨σ, hσ⟩, hV, hle⟩ := aux_plc_flex_facts M p i j0
  have hR : 0 ≤ M.flexBpb p i := by
    rw [← hσ]; exact div_nonneg (aux_plc_pieceSlope_nonneg M σ) (hp _).le
  have htail : ∀ j, ((M.util i j).tail : ℝ) ≤ M.flexBpb p i * p j := fun j => by
    have h := hle ⟨j, none⟩ (Or.inl ⟨j, le_rfl⟩)
    have e : M.pieceBpb p (⟨j, none⟩ : M.Piece i) = ((M.util i j).tail : ℝ) / p j := rfl
    rw [e, div_le_iff₀ (hp j)] at h; exact h
  have hnn : ∀ j, ∀ s ∈ (M.util i j).segs, (0:ℚ) ≤ s.2 :=
    fun j s hs => ((M.util i j).amount_pos s hs).le
  have hFeq : ∀ j, M.forcedAmount p i j = aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs :=
    fun j => aux_plc_forcedAmount M p i j (hp j)
  have hspent := aux_plc_spent_le M p hp i hle
  rw [aux_plc_spent, aux_plc_spentLP] at hspent
  simp_rw [hFeq] at hspent
  obtain ⟨xg, hxg1, hxg2, hxg3⟩ : ∃ xg : Fin g → ℝ,
      (∀ j, aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs ≤ xg j) ∧
      (∀ j, ((M.util i j).tail : ℝ) < M.flexBpb p i * p j →
        xg j ≤ aux_plc_G (M.flexBpb p i * p j) (M.util i j).segs) ∧
      ∑ j, p j * xg j = M.budget i := by
    rcases hV with ⟨j1, hj1⟩ | hV
    · have e : M.pieceBpb p (⟨j1, none⟩ : M.Piece i) = ((M.util i j1).tail : ℝ) / p j1 := rfl
      rw [e, le_div_iff₀ (hp j1)] at hj1
      refine ⟨fun j => aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs +
        if j = j1 then ((M.budget i : ℝ) -
          ∑ j, p j * aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs) / p j1 else 0,
          ?_, ?_, ?_⟩
      · intro j
        dsimp only
        split_ifs
        · have : 0 ≤ ((M.budget i : ℝ) -
              ∑ j, p j * aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs) / p j1 :=
            div_nonneg (by linarith) (hp j1).le
          linarith
        · linarith
      · intro j hj
        dsimp only
        split_ifs with h
        · subst h; linarith
        · rw [aux_plc_G_eq]; have := aux_plc_E_nonneg (M.flexBpb p i * p j) _ (hnn j); linarith
      · simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rw [mul_div_cancel₀ _ (hp j1).ne']
        ring
    · rw [aux_plc_vae_sum M p hp i] at hV
      set A := ∑ j, p j * aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs with hA
      set B := ∑ j, p j * aux_plc_G (M.flexBpb p i * p j) (M.util i j).segs with hB
      have hAB : A < B := lt_of_le_of_lt hspent hV
      set lam := ((M.budget i : ℝ) - A) / (B - A) with hlam
      have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
      have hlam1 : lam ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hGF : ∀ j, aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs ≤
          aux_plc_G (M.flexBpb p i * p j) (M.util i j).segs := fun j => by
        rw [aux_plc_G_eq]; have := aux_plc_E_nonneg (M.flexBpb p i * p j) _ (hnn j); linarith
      refine ⟨fun j => aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs +
        lam * (aux_plc_G (M.flexBpb p i * p j) (M.util i j).segs -
          aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs), ?_, ?_, ?_⟩
      · intro j
        have := mul_nonneg hlam0 (sub_nonneg.mpr (hGF j))
        simp only; linarith
      · intro j _
        have := mul_le_mul_of_nonneg_right hlam1 (sub_nonneg.mpr (hGF j))
        simp only; linarith
      · simp only [mul_add, Finset.sum_add_distrib]
        have e : ∑ j, p j * (lam * (aux_plc_G (M.flexBpb p i * p j) (M.util i j).segs -
            aux_plc_F (M.flexBpb p i * p j) (M.util i j).segs)) = lam * (B - A) := by
          rw [hA, hB, ← Finset.sum_sub_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        rw [e, hlam, div_mul_cancel₀ _ (by linarith : B - A ≠ 0)]
        ring
  have hxg0 : ∀ j, 0 ≤ xg j := fun j => le_trans (aux_plc_F_nonneg _ _ (hnn j)) (hxg1 j)
  have hopt := hx.2.2 xg hxg0 hxg3.le
  have hsup : ∀ j, (M.util i j).eval (x j) - (M.util i j).eval (xg j) ≤
      M.flexBpb p i * p j * (x j - xg j) :=
    fun j => aux_plc_sup (M.util i j) (M.flexBpb p i * p j) (M.flexBpb p i * p j) (xg j) (x j)
      (hxg0 j) (hx.1 j) (fun s _ => ⟨fun h => h.le, fun h => h, fun h => h.le⟩) (htail j)
      (fun h => h) (fun h => h.le) (hxg1 j) (hxg2 j)
  have hle0 : ∀ j ∈ (Finset.univ : Finset (Fin g)),
      (((M.util i j).eval (x j) - (M.util i j).eval (xg j)) -
        M.flexBpb p i * p j * (x j - xg j)) ≤ 0 := fun j _ => by linarith [hsup j]
  have hsum0 : 0 ≤ ∑ j, (((M.util i j).eval (x j) - (M.util i j).eval (xg j)) -
      M.flexBpb p i * p j * (x j - xg j)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e2 : ∑ j, M.flexBpb p i * p j * (x j - xg j) =
        M.flexBpb p i * (∑ j, p j * x j - ∑ j, p j * xg j) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e2, hxg3]
    have hbx := hx.2.1
    unfold utility at hopt
    have : M.flexBpb p i * (∑ j, p j * x j - M.budget i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hR (by linarith)
    linarith
  have hterm : ∀ j, M.flexBpb p i * p j * (x j - xg j) ≤
      (M.util i j).eval (x j) - (M.util i j).eval (xg j) := by
    intro j
    have h0 := le_antisymm (Finset.sum_nonpos hle0) hsum0
    have := (Finset.sum_eq_zero_iff_of_nonpos hle0).mp h0 j (Finset.mem_univ _)
    linarith
  obtain ⟨h1, h2⟩ := aux_plc_necgood (M.util i j) (M.flexBpb p i * p j) (xg j) (x j) (hxg0 j)
    (hx.1 j) (htail j) (hxg1 j) (hxg2 j) (hterm j)
  refine ⟨(hFeq j).symm ▸ h1, fun hnf => ?_⟩
  have hlt : ((M.util i j).tail : ℝ) < M.flexBpb p i * p j := by
    refine lt_of_le_of_ne (htail j) (fun h => hnf ?_)
    unfold IsFlexibleTail
    have e : M.pieceBpb p (⟨j, none⟩ : M.Piece i) = ((M.util i j).tail : ℝ) / p j := rfl
    rw [e, h, mul_div_cancel_right₀ _ (hp j).ne']
  have := h2 hlt
  rw [aux_plc_G_eq] at this
  rw [hFeq j]; exact this

lemma aux_plc_sufficiency (M : FisherMarket n g) (p' q : Fin g → ℝ) (hp' : ∀ j, 0 < p' j)
    (hq : ∀ j, 0 < q j) (i : Fin n) (j0 : Fin g)
    (h3a : ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i →
      M.pieceBpb p' τ = M.flexBpb p' i →
      (M.pieceSlope σ : ℝ) * q τ.1 = (M.pieceSlope τ : ℝ) * q σ.1)
    (h3b : ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i →
      M.flexBpb p' i < M.pieceBpb p' τ →
      (M.pieceSlope σ : ℝ) * q τ.1 ≤ (M.pieceSlope τ : ℝ) * q σ.1)
    (h3c : ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i →
      M.pieceBpb p' τ < M.flexBpb p' i →
      (M.pieceSlope τ : ℝ) * q σ.1 ≤ (M.pieceSlope σ : ℝ) * q τ.1)
    (x : Fin g → ℝ) (hx1 : ∀ j, M.forcedAmount p' i j ≤ x j)
    (hx2 : ∀ j, ¬ M.IsFlexibleTail p' i j →
      x j ≤ M.forcedAmount p' i j + aux_plc_E (M.flexBpb p' i * p' j) (M.util i j).segs)
    (hbud : ∑ j, q j * x j = M.budget i) :
    M.IsOptimalBundle q i x := by
  obtain ⟨⟨σ, hσ⟩, -, hle⟩ := aux_plc_flex_facts M p' i j0
  set R := M.flexBpb p' i with hRdef
  set r := (M.pieceSlope σ : ℝ) / q σ.1 with hr
  have hr0 : 0 ≤ r := div_nonneg (aux_plc_pieceSlope_nonneg M σ) (hq _).le
  have hqσ := hq σ.1
  have hnn : ∀ j, ∀ s ∈ (M.util i j).segs, (0:ℚ) ≤ s.2 :=
    fun j s hs => ((M.util i j).amount_pos s hs).le
  have hFeq : ∀ j, M.forcedAmount p' i j = aux_plc_F (R * p' j) (M.util i j).segs :=
    fun j => aux_plc_forcedAmount M p' i j (hp' j)
  have hx0 : ∀ j, 0 ≤ x j := fun j =>
    le_trans (by rw [hFeq]; exact aux_plc_F_nonneg _ _ (hnn j)) (hx1 j)
  refine ⟨hx0, hbud.le, fun y hy hyb => ?_⟩
  have hgood : ∀ j, (M.util i j).eval (y j) - (M.util i j).eval (x j) ≤
      r * q j * (y j - x j) := by
    intro j
    have eN : M.pieceBpb p' (⟨j, none⟩ : M.Piece i) = ((M.util i j).tail : ℝ) / p' j := rfl
    have eNs : M.pieceSlope (⟨j, none⟩ : M.Piece i) = (M.util i j).tail := rfl
    have htl : ((M.util i j).tail : ℝ) ≤ R * p' j := by
      have h := hle ⟨j, none⟩ (Or.inl ⟨j, le_rfl⟩)
      rw [eN, div_le_iff₀ (hp' j)] at h; exact h
    apply aux_plc_sup (M.util i j) (R * p' j) (r * q j) (x j) (y j) (hx0 j) (hy j)
    · intro s hs
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hs
      have eS : M.pieceBpb p' (⟨j, some k⟩ : M.Piece i) = (s.1 : ℝ) / p' j := by rw [← hk]; rfl
      have eSs : M.pieceSlope (⟨j, some k⟩ : M.Piece i) = s.1 := by rw [← hk]; rfl
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := h3b σ ⟨j, some k⟩ hσ (by rw [eS, lt_div_iff₀ (hp' j)]; exact h)
        rw [eSs] at this
        rw [hr, div_mul_eq_mul_div, div_le_iff₀ hqσ]; exact this
      · have := h3a σ ⟨j, some k⟩ hσ (by rw [eS, h, mul_div_cancel_right₀ _ (hp' j).ne'])
        rw [eSs] at this
        rw [hr, div_mul_eq_mul_div, eq_div_iff hqσ.ne']; linarith
      · have := h3c σ ⟨j, some k⟩ hσ (by rw [eS, div_lt_iff₀ (hp' j)]; exact h)
        rw [eSs] at this
        rw [hr, div_mul_eq_mul_div, le_div_iff₀ hqσ]; exact this
    · exact htl
    · intro h
      have := h3a σ ⟨j, none⟩ hσ (by rw [eN, h, mul_div_cancel_right₀ _ (hp' j).ne'])
      rw [eNs] at this
      rw [hr, div_mul_eq_mul_div, eq_div_iff hqσ.ne']; linarith
    · intro h
      have := h3c σ ⟨j, none⟩ hσ (by rw [eN, div_lt_iff₀ (hp' j)]; exact h)
      rw [eNs] at this
      rw [hr, div_mul_eq_mul_div, le_div_iff₀ hqσ]; exact this
    · rw [← hFeq]; exact hx1 j
    · intro h
      have hnf : ¬ M.IsFlexibleTail p' i j := by
        unfold IsFlexibleTail; rw [eN]; intro h'
        rw [div_eq_iff (hp' j).ne'] at h'; linarith
      rw [aux_plc_G_eq, ← hFeq]; exact hx2 j hnf
  unfold utility
  have hs : ∑ j, ((M.util i j).eval (y j) - (M.util i j).eval (x j)) ≤
      ∑ j, r * q j * (y j - x j) := Finset.sum_le_sum (fun j _ => hgood j)
  have e2 : ∑ j, r * q j * (y j - x j) = r * (∑ j, q j * y j - ∑ j, q j * x j) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_sub_distrib, e2, hbud] at hs
  have : r * (∑ j, q j * y j - M.budget i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith)
  linarith

end FisherMarket

end PLCMarkets.Rationality

open PLCMarkets.Rationality

theorem solution {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ))
    (z : FisherMarket.LPPoint n g) (hz : M.IsLPOptimal p' z)
    (hzpos : ∀ j, 0 < z.p j) :
    M.IsEquilibrium z.p := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · refine ⟨fun j => j.elim0, fun _ _ => 0, fun i => ⟨fun j => j.elim0, ?_, ?_⟩, fun j => j.elim0⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact_mod_cast (M.budget_pos i).le
    · intro y _ _; simp [FisherMarket.utility]
  have j0 : Fin g := ⟨0, hg⟩
  obtain ⟨-, xe, hxe_opt, hxe_clear⟩ := hp'
  have hnec := fun i j => FisherMarket.aux_plc_necessity M p' hpos i j0 (xe i) (hxe_opt i) j
  have hspentLP : ∀ i q, M.spentLP p' i q = ∑ j, q j * M.forcedAmount p' i j :=
    fun i q => FisherMarket.aux_plc_spentLP M p' q i
  set fm : Fin g → Fin n → ℝ := fun j i => p' j * (xe i j - M.forcedAmount p' i j) with hfm
  have hfm0 : ∀ j i, 0 ≤ fm j i := fun j i => mul_nonneg (hpos j).le (sub_nonneg.mpr (hnec i j).1)
  have hforced_le : ∀ j, M.forced p' j ≤ 1 := by
    intro j; unfold FisherMarket.forced; rw [← hxe_clear j]
    exact Finset.sum_le_sum (fun i _ => (hnec i j).1)
  have hfsrc : ∀ j, ∑ i, fm j i = M.unsold p' j * p' j := by
    intro j
    simp only [hfm, FisherMarket.unsold, FisherMarket.forced]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hxe_clear j]; ring
  have hwfeas : M.IsLPFeasible p' ⟨p', fun j => ∑ i, fm j i, fm, fun i => ∑ j, fm j i,
      ∑ j, ∑ i, fm j i⟩ := by
    refine ⟨?_, ?_, ?_, rfl, fun j => rfl, fun i => rfl, ?_, ?_, ?_, ?_, ?_, ?_, hsum, ?_, hfm0,
      ?_, ?_, fun j => (hpos j).le⟩
    · intro j; exact (hfsrc j).le
    · intro j i hnf
      show fm j i ≤ M.flexCapLP p' j i p'
      rw [FisherMarket.aux_plc_flexCapLP M p' p' i j (hpos j)]
      have h1 := (hnec i j).2 hnf
      have h2 : xe i j - M.forcedAmount p' i j ≤
          aux_plc_E (M.flexBpb p' i * p' j) (M.util i j).segs := by linarith
      have := mul_le_mul_of_nonneg_left h2 (hpos j).le
      simp only [hfm]; linarith
    · intro i
      show ∑ j, fm j i ≤ M.unspentLP p' i p'
      unfold FisherMarket.unspentLP; rw [hspentLP]
      simp only [hfm, mul_sub, Finset.sum_sub_distrib]
      have := (hxe_opt i).2.1; linarith
    · show ∑ i, ∑ j, fm j i = ∑ j, ∑ i, fm j i
      exact Finset.sum_comm
    · intro i σ τ hσ hτ
      show (M.pieceSlope σ : ℝ) * p' τ.1 = (M.pieceSlope τ : ℝ) * p' σ.1
      have : M.pieceBpb p' σ = M.pieceBpb p' τ := hσ.trans hτ.symm
      unfold FisherMarket.pieceBpb at this
      rw [div_eq_div_iff (hpos _).ne' (hpos _).ne'] at this; exact this
    · intro i σ τ hσ hτ
      show (M.pieceSlope σ : ℝ) * p' τ.1 ≤ (M.pieceSlope τ : ℝ) * p' σ.1
      have : M.pieceBpb p' σ < M.pieceBpb p' τ := hσ ▸ hτ
      unfold FisherMarket.pieceBpb at this
      rw [div_lt_div_iff₀ (hpos _) (hpos _)] at this; exact this.le
    · intro i σ τ hσ hτ
      show (M.pieceSlope τ : ℝ) * p' σ.1 ≤ (M.pieceSlope σ : ℝ) * p' τ.1
      have : M.pieceBpb p' τ < M.pieceBpb p' σ := hσ ▸ hτ
      unfold FisherMarket.pieceBpb at this
      rw [div_lt_div_iff₀ (hpos _) (hpos _)] at this; exact this.le
    · intro i
      show 0 ≤ M.unspentLP p' i p'
      unfold FisherMarket.unspentLP
      have := FisherMarket.aux_plc_spent_le M p' hpos i
        (FisherMarket.aux_plc_flex_facts M p' i j0).2.2
      rw [FisherMarket.aux_plc_spent] at this; linarith
    · intro j; unfold FisherMarket.unsold; linarith [hforced_le j]
    · intro j; show 0 ≤ ∑ i, fm j i; exact Finset.sum_nonneg (fun i _ => hfm0 j i)
    · intro i; show 0 ≤ ∑ j, fm j i; exact Finset.sum_nonneg (fun j _ => hfm0 j i)
    · show 0 ≤ ∑ j, ∑ i, fm j i
      exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hfm0 j i))
  have hwobj : M.lpObjective p' ⟨p', fun j => ∑ i, fm j i, fm, fun i => ∑ j, fm j i,
      ∑ j, ∑ i, fm j i⟩ = ∑ i, (M.budget i : ℝ) := by
    unfold FisherMarket.lpObjective
    show ∑ j, ∑ i, fm j i + ∑ i, M.spentLP p' i p' = _
    simp_rw [hfsrc, hspentLP]
    rw [Finset.sum_comm (f := fun i j => p' j * M.forcedAmount p' i j)]
    rw [← hsum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    unfold FisherMarket.unsold FisherMarket.forced
    rw [← Finset.mul_sum]; ring
  obtain ⟨hzf, hzopt⟩ := hz
  have hzobj := hzopt _ hwfeas
  rw [hwobj] at hzobj
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, hz16,
    hz17, hz18⟩ := hzf
  unfold FisherMarket.lpObjective at hzobj
  have hsnk : ∀ i, z.fsnk i = M.unspentLP p' i z.p := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), z.fsnk i - M.unspentLP p' i z.p ≤ 0 :=
      fun i _ => by linarith [hz3 i]
    have hsum0 : ∑ i, (z.fsnk i - M.unspentLP p' i z.p) = 0 := by
      apply le_antisymm (Finset.sum_nonpos hle)
      rw [Finset.sum_sub_distrib]
      unfold FisherMarket.unspentLP
      rw [Finset.sum_sub_distrib]
      linarith
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum0 i (Finset.mem_univ _)
    linarith
  have hsrc : ∀ j, z.fsrc j = M.unsold p' j * z.p j := by
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin g)), z.fsrc j - M.unsold p' j * z.p j ≤ 0 :=
      fun j _ => by linarith [hz1 j]
    have hsum0 : ∑ j, (z.fsrc j - M.unsold p' j * z.p j) = 0 := by
      apply le_antisymm (Finset.sum_nonpos hle)
      rw [Finset.sum_sub_distrib, ← hz4]
      have e : ∑ j, M.unsold p' j * z.p j =
          ∑ i, (M.budget i : ℝ) - ∑ i, M.spentLP p' i z.p := by
        simp_rw [hspentLP]
        rw [Finset.sum_comm (f := fun i j => z.p j * M.forcedAmount p' i j), ← hz13,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _
        unfold FisherMarket.unsold FisherMarket.forced
        rw [← Finset.mul_sum]; ring
      rw [e]; linarith
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum0 j (Finset.mem_univ _)
    linarith
  refine ⟨fun j => (hzpos j).le, fun i j => M.forcedAmount p' i j + z.fmid j i / z.p j,
    fun i => ?_, fun j => ?_⟩
  · apply FisherMarket.aux_plc_sufficiency M p' z.p hpos hzpos i j0 (hz8 i) (hz9 i) (hz10 i)
    · intro j; have := div_nonneg (hz15 j i) (hzpos j).le; linarith
    · intro j hnf
      have h := hz2 j i hnf
      rw [FisherMarket.aux_plc_flexCapLP M p' z.p i j (hpos j)] at h
      have : z.fmid j i / z.p j ≤ aux_plc_E (M.flexBpb p' i * p' j) (M.util i j).segs := by
        rw [div_le_iff₀ (hzpos j)]; exact h
      linarith
    · simp only [mul_add, Finset.sum_add_distrib]
      have e : ∑ j, z.p j * (z.fmid j i / z.p j) = z.fsnk i := by
        rw [← hz6 i]; apply Finset.sum_congr rfl; intro j _
        exact mul_div_cancel₀ _ (hzpos j).ne'
      rw [e, hsnk i, ← hspentLP]; unfold FisherMarket.unspentLP; ring
  · rw [Finset.sum_add_distrib, ← Finset.sum_div, ← hz5 j, hsrc j,
      mul_div_cancel_right₀ _ (hzpos j).ne']
    unfold FisherMarket.unsold FisherMarket.forced
    ring
