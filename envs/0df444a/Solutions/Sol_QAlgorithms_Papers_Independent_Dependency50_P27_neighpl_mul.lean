-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.neighpl_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:31:49.034444+00:00
-- url     : https://prove2.me/submissions/1de4a473-c75d-440d-a5cd-fe8da9092396

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27
namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

lemma S171Q_cross {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (a c x : R) (hx : x ∈ crossingRoot p a c) : a < x ∧ x < c := by
  unfold crossingRoot at hx
  split_ifs at hx with h1 h2
  · simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨ha, hb, he⟩ := (PolynomialIVT.root p a c h1.1 (le_of_lt h1.2.1) (le_of_lt h1.2.2)).property
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · intro h; rw [← h] at he; exact absurd he h1.2.1.ne
    · intro h; rw [h] at he; exact absurd he h1.2.2.ne'
  · simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨ha, hb, he⟩ := (PolynomialIVT.root (-p) a c h2.1 (le_of_lt h2.2.1) (le_of_lt h2.2.2)).property
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · intro h; rw [← h] at he; exact absurd he h2.2.1.ne
    · intro h; rw [h] at he; exact absurd he h2.2.2.ne'
  · simp at hx

lemma S171Q_cross_pw {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (a c : R) : (crossingRoot p a c).Pairwise (· < ·) := by
  unfold crossingRoot
  split_ifs <;> simp

lemma S171Q_scan {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (p : Polynomial R) (cs : List R) : ∀ a : R, (a :: cs).Pairwise (· < ·) →
    (scanCells p a cs).Pairwise (· < ·) ∧ ∀ x ∈ scanCells p a cs, a < x := by
  induction cs with
  | nil => intro a _; simp [scanCells]
  | cons c cs ih =>
    intro a h
    have hac : a < c := List.rel_of_pairwise_cons h (by simp)
    obtain ⟨ih1, ih2⟩ := ih c (List.Pairwise.of_cons h)
    have hmid : ∀ x ∈ (if p.eval c = 0 then [c] else []), x = c := by
      intro x hx; split_ifs at hx <;> simp_all
    have hmidpw : (if p.eval c = 0 then [c] else []).Pairwise (· < ·) := by split_ifs <;> simp
    simp only [scanCells]
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨S171Q_cross_pw p a c, hmidpw, ?_⟩, ih1, ?_⟩
      · intro x hx y hy
        rw [hmid y hy]; exact (S171Q_cross p a c x hx).2
      · intro x hx y hy
        rcases List.mem_append.1 hx with hx | hx
        · exact lt_trans (S171Q_cross p a c x hx).2 (ih2 y hy)
        · rw [hmid x hx]; exact ih2 y hy
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · exact (S171Q_cross p a c x hx).1
        · rw [hmid x hx]; exact hac
      · exact lt_trans hac (ih2 x hx)

lemma S171Q_aux {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]
    (a b : R) (n : ℕ) : ∀ p : Polynomial R, (rootsAux n p a b).Pairwise (· < ·) ∧
      ∀ x ∈ rootsAux n p a b, a < x ∧ x < b := by
  induction n with
  | zero => intro p; simp [rootsAux]
  | succ n ih =>
    intro p
    simp only [rootsAux]
    split_ifs with h
    · simp
    · push Not at h
      obtain ⟨ih1, ih2⟩ := ih p.derivative
      have hpw : (a :: (rootsAux n p.derivative a b ++ [b])).Pairwise (· < ·) := by
        rw [List.pairwise_cons, List.pairwise_append]
        refine ⟨?_, ih1, by simp, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact (ih2 x hx).1
          · simp at hx; rw [hx]; exact h.2
        · intro x hx y hy
          simp at hy; rw [hy]; exact (ih2 x hx).2
      refine ⟨(S171Q_scan p _ a hpw).1.filter _, ?_⟩
      intro x hx
      simpa using (List.mem_filter.1 hx).2


section S173G
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [PolynomialIVT R]

lemma S173G_ivt_up (f : R[X]) {a b : R} (hab : a ≤ b) (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f.eval x = 0 :=
  let r := PolynomialIVT.root f a b hab ha hb
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩

lemma S173G_ivt_down (f : R[X]) {a b : R} (hab : a ≤ b) (ha : 0 ≤ f.eval a) (hb : f.eval b ≤ 0) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f.eval x = 0 := by
  obtain ⟨x, h1, h2, h3⟩ := S173G_ivt_up (-f) hab (by simp; linarith) (by simp; linarith)
  exact ⟨x, h1, h2, by simpa using h3⟩

/-- Core: r(a) = r(s) = 0, no roots of r strictly between, then r' vanishes strictly between. -/
lemma S173G_core (r : R[X]) (hr : r ≠ 0) {a s : R} (has : a < s) (ha : r.eval a = 0)
    (hs : r.eval s = 0) (hno : ∀ x, a < x → x < s → r.eval x ≠ 0) :
    ∃ c, a < c ∧ c < s ∧ r.derivative.eval c = 0 := by
  obtain ⟨q1, hq1, hq1a⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr a
  have hm : 0 < rootMultiplicity a r := (rootMultiplicity_pos hr).mpr ha
  have hq1ne : q1 ≠ 0 := by rintro rfl; simp at hq1; exact hr hq1
  have hq1s : q1.eval s = 0 := by
    have := hs; rw [hq1, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff hm.ne' |>.mp h) (sub_ne_zero.mpr has.ne')
    · exact h
  obtain ⟨q, hq, hqs⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q1 hq1ne s
  have hk : 0 < rootMultiplicity s q1 := (rootMultiplicity_pos hq1ne).mpr hq1s
  set m := rootMultiplicity a r
  set k := rootMultiplicity s q1
  have hqs0 : q.eval s ≠ 0 := by
    intro h; apply hqs; exact dvd_iff_isRoot.mpr h
  have hqa0 : q.eval a ≠ 0 := by
    intro h; apply hq1a; rw [hq]
    exact dvd_mul_of_dvd_right (dvd_iff_isRoot.mpr h) _
  have hrq : r = (X - C a) ^ m * ((X - C s) ^ k * q) := by rw [hq1, hq]
  -- q has no root in [a, s]
  have hqno : ∀ x, a ≤ x → x ≤ s → q.eval x ≠ 0 := by
    intro x hx1 hx2 hx
    rcases hx1.lt_or_eq with hx1 | rfl
    · rcases hx2.lt_or_eq with hx2 | rfl
      · apply hno x hx1 hx2; rw [hrq]; simp [hx]
      · exact hqs0 hx
    · exact hqa0 hx
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set g : R[X] := C ((m' : R) + 1) * (X - C s) * q + C ((k' : R) + 1) * (X - C a) * q +
    (X - C a) * (X - C s) * q.derivative
  have hder : ∀ c, r.derivative.eval c = (c - a) ^ m' * (c - s) ^ k' * g.eval c := by
    intro c
    rw [hrq, hm', hk']
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
      eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C, eval_natCast, g, mul_one]
    push_cast
    ring
  have hga : g.eval a = ((m' : R) + 1) * (a - s) * q.eval a := by simp [g]
  have hgs : g.eval s = ((k' : R) + 1) * (s - a) * q.eval s := by simp [g]
  have hm1 : (0 : R) < (m' : R) + 1 := by positivity
  have hk1 : (0 : R) < (k' : R) + 1 := by positivity
  have hsa : (0 : R) < s - a := sub_pos.mpr has
  have hgroot : ∃ c, a ≤ c ∧ c ≤ s ∧ g.eval c = 0 := by
    rcases lt_or_gt_of_ne hqa0 with hqa | hqa
    · -- q a < 0, then q s < 0
      have hqs' : q.eval s < 0 := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨x, h1, h2, h3⟩ := S173G_ivt_up q has.le hqa.le hcon
        exact hqno x h1 h2 h3
      apply S173G_ivt_down g has.le
      · rw [hga]; have : 0 < ((m' : R) + 1) * (s - a) := mul_pos hm1 hsa; nlinarith
      · rw [hgs]; have : 0 < ((k' : R) + 1) * (s - a) := mul_pos hk1 hsa; nlinarith
    · have hqs' : 0 < q.eval s := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨x, h1, h2, h3⟩ := S173G_ivt_down q has.le hqa.le hcon
        exact hqno x h1 h2 h3
      apply S173G_ivt_up g has.le
      · rw [hga]; have : 0 < ((m' : R) + 1) * (s - a) := mul_pos hm1 hsa; nlinarith
      · rw [hgs]; have : 0 < ((k' : R) + 1) * (s - a) := mul_pos hk1 hsa; nlinarith
  obtain ⟨c, hc1, hc2, hc3⟩ := hgroot
  have hca : c ≠ a := by
    rintro rfl; rw [hga] at hc3
    have : ((m' : R) + 1) * (c - s) ≠ 0 := mul_ne_zero hm1.ne' (sub_ne_zero.mpr has.ne)
    exact mul_ne_zero this hqa0 hc3
  have hcs : c ≠ s := by
    rintro rfl; rw [hgs] at hc3
    have : ((k' : R) + 1) * (c - a) ≠ 0 := mul_ne_zero hk1.ne' hsa.ne'
    exact mul_ne_zero this hqs0 hc3
  exact ⟨c, lt_of_le_of_ne hc1 (Ne.symm hca), lt_of_le_of_ne hc2 hcs, by rw [hder, hc3, mul_zero]⟩

theorem S173G_rolle (a b : R) (p : Polynomial R)
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c : R, a < c ∧ c < b ∧ p.derivative.eval c = 0 := by
  set r := p - C (p.eval a)
  have hder : r.derivative = p.derivative := by simp [r]
  have hra : r.eval a = 0 := by simp [r]
  have hrb : r.eval b = 0 := by simp [r, heq]
  by_cases hr : r = 0
  · refine ⟨(a + b) / 2, by linarith, by linarith, ?_⟩
    rw [← hder, hr]; simp
  set S := r.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)
  have hbS : b ∈ S := by
    simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hr, IsRoot.def]
    exact ⟨hrb, hab, le_refl _⟩
  have hne : S.Nonempty := ⟨b, hbS⟩
  set s := S.min' hne
  have hsS : s ∈ S := S.min'_mem hne
  simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hr, IsRoot.def] at hsS
  obtain ⟨hrs, has, hsb⟩ := hsS
  have hno : ∀ x, a < x → x < s → r.eval x ≠ 0 := by
    intro x hx1 hx2 hx
    have : x ∈ S := by
      simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hr, IsRoot.def]
      exact ⟨hx, hx1, le_trans hx2.le hsb⟩
    have := S.min'_le x this
    exact absurd hx2 (not_lt.mpr this)
  obtain ⟨c, hc1, hc2, hc3⟩ := S173G_core r hr has hra hrs hno
  exact ⟨c, hc1, lt_of_lt_of_le hc2 hsb, by rw [← hder]; exact hc3⟩
theorem S173G_mvt (a b : R) (p : Polynomial R) (hab : a < b) :
    ∃ c : R, a < c ∧ c < b ∧
      p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  set g : R[X] := C (b - a) * p - C (p.eval b - p.eval a) * X
  have heq : g.eval a = g.eval b := by simp [g]; ring
  obtain ⟨c, h1, h2, h3⟩ := S173G_rolle a b g hab heq
  refine ⟨c, h1, h2, ?_⟩
  simp [g] at h3
  linear_combination -h3

theorem S173G_strict (qs : List (Polynomial R))
    (h : ∃ x : R, ∀ q ∈ qs, 0 < q.eval x) :
    ∃ y : R, (∀ q ∈ qs, 0 < q.eval y) ∧
      ((∀ q ∈ qs, ∀ r : R, q.eval r = 0 → r < y) ∨
       (∀ q ∈ qs, ∀ r : R, q.eval r = 0 → y < r) ∨
       qs.prod.derivative.eval y = 0) := by
  obtain ⟨x, hx⟩ := h
  set P := qs.prod
  have hPeval : ∀ t, P.eval t = (qs.map (fun q => q.eval t)).prod := fun t => eval_list_prod _ _
  have hroot : ∀ q ∈ qs, ∀ r, q.eval r = 0 → P.eval r = 0 := by
    intro q hq r hr
    rw [hPeval]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨q, hq, hr⟩)
  have hPx : P.eval x ≠ 0 := by
    rw [hPeval]
    intro h0
    obtain ⟨t, ht, ht0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    exact (hx t ht).ne' ht0
  have hP0 : P ≠ 0 := by rintro h0; rw [h0] at hPx; simp at hPx
  set U := P.roots.toFinset.filter (fun r => x < r)
  set L := P.roots.toFinset.filter (fun r => r < x)
  by_cases hU : U.Nonempty
  · by_cases hL : L.Nonempty
    · set r2 := U.min' hU
      set r1 := L.max' hL
      have hr2 := U.min'_mem hU
      have hr1 := L.max'_mem hL
      simp only [U, L, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def] at hr1 hr2
      obtain ⟨hP2, hx2⟩ := hr2
      obtain ⟨hP1, hx1⟩ := hr1
      have hnoP : ∀ t, r1 < t → t < r2 → P.eval t ≠ 0 := by
        intro t ht1 ht2 ht
        rcases lt_trichotomy t x with htx | rfl | htx
        · have : t ∈ L := by
            simp only [L, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
            exact ⟨ht, htx⟩
          exact absurd ht1 (not_lt.mpr (L.le_max' t this))
        · exact hPx ht
        · have : t ∈ U := by
            simp only [U, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
            exact ⟨ht, htx⟩
          exact absurd ht2 (not_lt.mpr (U.min'_le t this))
      obtain ⟨c, hc1, hc2, hc3⟩ := S173G_rolle r1 r2 P (hx1.trans hx2) (by rw [hP1, hP2])
      refine ⟨c, ?_, Or.inr (Or.inr hc3)⟩
      intro q hq
      by_contra hcon
      push_neg at hcon
      have hqx := hx q hq
      rcases le_total c x with hcx | hcx
      · obtain ⟨t, ht1, ht2, ht3⟩ := S173G_ivt_up q hcx hcon hqx.le
        exact hnoP t (lt_of_lt_of_le hc1 ht1) (lt_of_le_of_lt ht2 hx2) (hroot q hq t ht3)
      · obtain ⟨t, ht1, ht2, ht3⟩ := S173G_ivt_down q hcx hqx.le hcon
        exact hnoP t (lt_of_lt_of_le hx1 ht1) (lt_of_le_of_lt ht2 hc2) (hroot q hq t ht3)
    · refine ⟨x, hx, Or.inr (Or.inl ?_)⟩
      intro q hq r hr
      have hPr := hroot q hq r hr
      rcases lt_trichotomy r x with hrx | rfl | hrx
      · exact absurd ⟨r, by
          simp only [L, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
          exact ⟨hPr, hrx⟩⟩ hL
      · exact absurd hr (hx q hq).ne'
      · exact hrx
  · refine ⟨x, hx, Or.inl ?_⟩
    intro q hq r hr
    have hPr := hroot q hq r hr
    rcases lt_trichotomy r x with hrx | rfl | hrx
    · exact hrx
    · exact absurd hr (hx q hq).ne'
    · exact absurd ⟨r, by
        simp only [U, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
        exact ⟨hPr, hrx⟩⟩ hU
lemma S173H_deriv_sign (p : R[X]) {u v : R} (huv : u < v)
    (hno : ∀ y, u < y → y < v → p.derivative.eval y ≠ 0) :
    (∀ y, u < y → y < v → 0 < p.derivative.eval y) ∨
    (∀ y, u < y → y < v → p.derivative.eval y < 0) := by
  set m := (u + v) / 2
  have hm1 : u < m := by simp only [m]; linarith
  have hm2 : m < v := by simp only [m]; linarith
  rcases lt_or_gt_of_ne (hno m hm1 hm2) with hneg | hpos
  · right
    intro y hy1 hy2
    by_contra hcon; push_neg at hcon
    rcases le_total y m with hym | hym
    · obtain ⟨z, h1, h2, h3⟩ := S173G_ivt_down p.derivative hym hcon hneg.le
      exact hno z (lt_of_lt_of_le hy1 h1) (lt_of_le_of_lt h2 hm2) h3
    · obtain ⟨z, h1, h2, h3⟩ := S173G_ivt_up p.derivative hym hneg.le hcon
      exact hno z (lt_of_lt_of_le hm1 h1) (lt_of_le_of_lt h2 hy2) h3
  · left
    intro y hy1 hy2
    by_contra hcon; push_neg at hcon
    rcases le_total y m with hym | hym
    · obtain ⟨z, h1, h2, h3⟩ := S173G_ivt_up p.derivative hym hcon hpos.le
      exact hno z (lt_of_lt_of_le hy1 h1) (lt_of_le_of_lt h2 hm2) h3
    · obtain ⟨z, h1, h2, h3⟩ := S173G_ivt_down p.derivative hym hpos.le hcon
      exact hno z (lt_of_lt_of_le hm1 h1) (lt_of_le_of_lt h2 hy2) h3

lemma S173H_mono (p : R[X]) {u v : R} (huv : u < v)
    (hno : ∀ y, u < y → y < v → p.derivative.eval y ≠ 0) :
    (∀ s t, u ≤ s → s < t → t ≤ v → p.eval s < p.eval t) ∨
    (∀ s t, u ≤ s → s < t → t ≤ v → p.eval t < p.eval s) := by
  rcases S173H_deriv_sign p huv hno with h | h
  · left
    intro s t hs hst ht
    obtain ⟨c, hc1, hc2, hc3⟩ := S173G_mvt s t p hst
    have := h c (lt_of_le_of_lt hs hc1) (lt_of_lt_of_le hc2 ht)
    have : 0 < p.derivative.eval c * (t - s) := mul_pos this (sub_pos.mpr hst)
    linarith
  · right
    intro s t hs hst ht
    obtain ⟨c, hc1, hc2, hc3⟩ := S173G_mvt s t p hst
    have := h c (lt_of_le_of_lt hs hc1) (lt_of_lt_of_le hc2 ht)
    have : p.derivative.eval c * (t - s) < 0 := mul_neg_of_neg_of_pos this (sub_pos.mpr hst)
    linarith

lemma S173H_cross_root (p : R[X]) (u v x : R) (hx : x ∈ crossingRoot p u v) : p.eval x = 0 := by
  unfold crossingRoot at hx
  split_ifs at hx with h1 h2
  · simp only [List.mem_singleton] at hx; subst hx
    exact (PolynomialIVT.root p u v h1.1 (le_of_lt h1.2.1) (le_of_lt h1.2.2)).property.2.2
  · simp only [List.mem_singleton] at hx; subst hx
    have := (PolynomialIVT.root (-p) u v h2.1 (le_of_lt h2.2.1) (le_of_lt h2.2.2)).property.2.2
    simpa using this
  · simp at hx

lemma S173H_cross_mem (p : R[X]) {u v x : R} (hux : u < x) (hxv : x < v) (hpx : p.eval x = 0)
    (hno : ∀ y, u < y → y < v → p.derivative.eval y ≠ 0) : x ∈ crossingRoot p u v := by
  have huv : u < v := hux.trans hxv
  rcases S173H_mono p huv hno with hinc | hdec
  · have h1 : p.eval u < 0 := hpx ▸ hinc u x le_rfl hux hxv.le
    have h2 : 0 < p.eval v := hpx ▸ hinc x v hux.le hxv le_rfl
    unfold crossingRoot
    rw [dif_pos ⟨huv.le, h1, h2⟩]
    obtain ⟨hy1, hy2, hy3⟩ := (PolynomialIVT.root p u v huv.le h1.le h2.le).property
    set y := (PolynomialIVT.root p u v huv.le h1.le h2.le).val
    simp only [List.mem_singleton]
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hinc x y hux.le h hy2; linarith
    · have := hinc y x hy1 h hxv.le; linarith
  · have h1 : 0 < p.eval u := hpx ▸ hdec u x le_rfl hux hxv.le
    have h2 : p.eval v < 0 := hpx ▸ hdec x v hux.le hxv le_rfl
    unfold crossingRoot
    rw [dif_neg (by intro h; linarith [h.2.1]), dif_pos ⟨huv.le, by simp; linarith, by simp; linarith⟩]
    have hh : u ≤ v ∧ (-p).eval u < 0 ∧ 0 < (-p).eval v := ⟨huv.le, by simp; linarith, by simp; linarith⟩
    obtain ⟨hy1, hy2, hy3⟩ := (PolynomialIVT.root (-p) u v hh.1 hh.2.1.le hh.2.2.le).property
    set y := (PolynomialIVT.root (-p) u v hh.1 hh.2.1.le hh.2.2.le).val
    simp only [List.mem_singleton]
    simp at hy3
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hdec x y hux.le h hy2; linarith
    · have := hdec y x hy1 h hxv.le; linarith

lemma S173H_scan_sound (p : R[X]) (cs : List R) : ∀ a x, x ∈ scanCells p a cs → p.eval x = 0 := by
  induction cs with
  | nil => intro a x hx; simp [scanCells] at hx
  | cons c cs ih =>
    intro a x hx
    simp only [scanCells, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact S173H_cross_root p a c x hx
    · split_ifs at hx with h
      · simp at hx; rw [hx]; exact h
      · simp at hx
    · exact ih c x hx

lemma S173H_scan_complete (p : R[X]) (cs : List R) : ∀ a, (a :: cs).Pairwise (· < ·) →
    (∀ y, a < y → p.derivative.eval y = 0 → (∃ c ∈ cs, y ≤ c) → y ∈ cs) →
    ∀ x, a < x → p.eval x = 0 → (∃ c ∈ cs, x ≤ c) → x ∈ scanCells p a cs := by
  induction cs with
  | nil => intro a _ _ x _ _ hc; simp at hc
  | cons c cs ih =>
    intro a hpw hH x hax hpx hc
    have hac : a < c := List.rel_of_pairwise_cons hpw (by simp)
    have hcs : ∀ d ∈ cs, c < d := fun d hd => List.rel_of_pairwise_cons (List.Pairwise.of_cons hpw) hd
    simp only [scanCells, List.mem_append]
    rcases lt_trichotomy x c with hxc | rfl | hxc
    · left; left
      refine S173H_cross_mem p hax hxc hpx ?_
      intro y hy1 hy2 hy3
      have := hH y hy1 hy3 ⟨c, by simp, hy2.le⟩
      simp only [List.mem_cons] at this
      rcases this with rfl | hy
      · exact lt_irrefl _ hy2
      · exact lt_irrefl _ (lt_trans hy2 (hcs y hy))
    · left; right; simp [hpx]
    · right
      obtain ⟨d, hd, hxd⟩ := hc
      simp only [List.mem_cons] at hd
      have hd' : d ∈ cs := by
        rcases hd with rfl | hd
        · exact absurd hxd (not_le.mpr hxc)
        · exact hd
      refine ih c (List.Pairwise.of_cons hpw) ?_ x hxc hpx ⟨d, hd', hxd⟩
      intro y hy1 hy2 ⟨e, he, hye⟩
      have := hH y (hac.trans hy1) hy2 ⟨e, by simp [he], hye⟩
      simp only [List.mem_cons] at this
      rcases this with rfl | hy
      · exact absurd hy1 (lt_irrefl _)
      · exact hy

lemma S173H_aux (a b : R) (n : ℕ) : ∀ p : R[X], p ≠ 0 → p.natDegree < n →
    rootsOn p a b (rootsAux n p a b) := by
  induction n with
  | zero => intro p _ h; omega
  | succ n ih =>
    intro p hp hdeg
    obtain ⟨hpw0, hin0⟩ := S171Q_aux a b n p.derivative
    simp only [rootsAux]
    split_ifs with h
    · rcases h with h | h
      · exact absurd h hp
      · intro x; simp only [List.not_mem_nil, false_iff]
        rintro ⟨h1, h2, _⟩; exact absurd (h1.trans h2) (not_lt.mpr h)
    · push Not at h
      have hab := h.2
      intro x
      rw [List.mem_filter]
      constructor
      · rintro ⟨hx, hx2⟩
        simp only [decide_eq_true_eq] at hx2
        exact ⟨hx2.1, hx2.2, S173H_scan_sound p _ a x hx⟩
      · rintro ⟨hx1, hx2, hx3⟩
        refine ⟨?_, by simp [hx1, hx2]⟩
        by_cases hd0 : p.derivative = 0
        · exfalso
          have hc := eq_C_of_derivative_eq_zero hd0
          rw [hc] at hx3 hp
          simp only [eval_C] at hx3
          exact hp (by rw [hx3, C_0])
        have hdeg' : p.derivative.natDegree < n := by
          have hne : p.natDegree ≠ 0 := by
            intro h0; apply hd0
            rw [eq_C_of_natDegree_eq_zero h0]; simp
          have := natDegree_derivative_lt hne
          omega
        have hIH := ih p.derivative hd0 hdeg'
        have hpw : (a :: (rootsAux n p.derivative a b ++ [b])).Pairwise (· < ·) := by
          rw [List.pairwise_cons, List.pairwise_append]
          refine ⟨?_, hpw0, by simp, ?_⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact (hin0 x hx).1
            · simp at hx; rw [hx]; exact hab
          · intro x hx y hy
            simp at hy; rw [hy]; exact (hin0 x hx).2
        refine S173H_scan_complete p _ a hpw ?_ x hx1 hx3 ⟨b, by simp, hx2.le⟩
        intro y hy1 hy2 ⟨c, hc, hyc⟩
        have hcb : c ≤ b := by
          rcases List.mem_append.1 hc with hc | hc
          · exact (hin0 c hc).2.le
          · simp at hc; rw [hc]
        rcases (hyc.trans hcb).lt_or_eq with hyb | rfl
        · exact List.mem_append_left _ ((hIH y).mpr ⟨hy1, hyb, hy2⟩)
        · simp

theorem S173H_roots_on (p : Polynomial R) (a b : R) (hp : p ≠ 0) :
    rootsOn p a b (roots p a b) := S173H_aux a b _ p hp (Nat.lt_succ_self _)


lemma S173I_head (l : List R) (d : R) (hl : l.Pairwise (· < ·)) (hne : l ≠ []) :
    l.headD d ∈ l ∧ ∀ x ∈ l, l.headD d ≤ x := by
  cases l with
  | nil => exact absurd rfl hne
  | cons h t =>
    simp only [List.headD_cons, List.mem_cons, true_or, true_and]
    rintro x (rfl | hx)
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hl hx).le

lemma S173I_last (l : List R) (d : R) (hl : l.Pairwise (· < ·)) (hne : l ≠ []) :
    l.reverse.headD d ∈ l ∧ ∀ x ∈ l, x ≤ l.reverse.headD d := by
  have hl' : l.reverse.Pairwise (· > ·) := List.pairwise_reverse.mpr hl
  cases hr : l.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hne
  | cons h t =>
    rw [hr] at hl'
    simp only [List.headD_cons]
    have hmem : ∀ x, x ∈ l ↔ x ∈ h :: t := fun x => by rw [← hr, List.mem_reverse]
    refine ⟨(hmem h).mpr (by simp), ?_⟩
    intro x hx
    rcases List.mem_cons.mp ((hmem x).mp hx) with rfl | hx'
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hl' hx').le

lemma S173I_next_char (f : R[X]) (a b : R) (hf : f ≠ 0) :
    (nextRoot f a b = max b a ∨ (a < nextRoot f a b ∧ nextRoot f a b < b ∧ f.eval (nextRoot f a b) = 0)) ∧
    ∀ r, a < r → r < b → f.eval r = 0 → nextRoot f a b ≤ r := by
  have hon := S173H_roots_on f a b hf
  have hs := S171Q_aux a b (f.natDegree + 1) f
  unfold nextRoot
  rw [if_neg hf]
  by_cases hl : roots f a b = []
  · rw [hl]
    refine ⟨Or.inl rfl, fun r h1 h2 h3 => ?_⟩
    have := (hon r).mpr ⟨h1, h2, h3⟩
    rw [hl] at this; simp at this
  · obtain ⟨hm, hmin⟩ := S173I_head (roots f a b) (max b a) hs.1 hl
    obtain ⟨h1, h2, h3⟩ := (hon _).mp hm
    exact ⟨Or.inr ⟨h1, h2, h3⟩, fun r r1 r2 r3 => hmin r ((hon r).mpr ⟨r1, r2, r3⟩)⟩

lemma S173I_prev_char (f : R[X]) (a b : R) (hf : f ≠ 0) :
    (prevRoot f a b = min a b ∨ (a < prevRoot f a b ∧ prevRoot f a b < b ∧ f.eval (prevRoot f a b) = 0)) ∧
    ∀ r, a < r → r < b → f.eval r = 0 → r ≤ prevRoot f a b := by
  have hon := S173H_roots_on f a b hf
  have hs := S171Q_aux a b (f.natDegree + 1) f
  unfold prevRoot
  rw [if_neg hf]
  by_cases hl : roots f a b = []
  · rw [hl]
    refine ⟨Or.inl rfl, fun r h1 h2 h3 => ?_⟩
    have := (hon r).mpr ⟨h1, h2, h3⟩
    rw [hl] at this; simp at this
  · obtain ⟨hm, hmax⟩ := S173I_last (roots f a b) (min a b) hs.1 hl
    obtain ⟨h1, h2, h3⟩ := (hon _).mp hm
    exact ⟨Or.inr ⟨h1, h2, h3⟩, fun r r1 r2 r3 => hmax r ((hon r).mpr ⟨r1, r2, r3⟩)⟩

lemma S173I_next_ge (f : R[X]) (a b : R) : a ≤ nextRoot f a b := by
  by_cases hf : f = 0
  · unfold nextRoot; rw [if_pos hf]
  · rcases (S173I_next_char f a b hf).1 with h | h
    · rw [h]; exact le_max_right _ _
    · exact h.1.le

lemma S173I_next_le (f : R[X]) (a b : R) (hf : f ≠ 0) : nextRoot f a b ≤ max b a := by
  rcases (S173I_next_char f a b hf).1 with h | h
  · rw [h]
  · exact h.2.1.le.trans (le_max_left _ _)

lemma S173I_prev_le (f : R[X]) (a b : R) : prevRoot f a b ≤ b := by
  by_cases hf : f = 0
  · unfold prevRoot; rw [if_pos hf]
  · rcases (S173I_prev_char f a b hf).1 with h | h
    · rw [h]; exact min_le_right _ _
    · exact h.2.1.le

lemma S173I_prev_ge (f : R[X]) (a b : R) (hf : f ≠ 0) : min a b ≤ prevRoot f a b := by
  rcases (S173I_prev_char f a b hf).1 with h | h
  · rw [h]
  · exact (min_le_left _ _).trans h.1.le

theorem S173I_next_mul (a b : R) (p q : Polynomial R) :
    nextRoot (p * q) a b = min (nextRoot p a b) (nextRoot q a b) := by
  by_cases hp : p = 0
  · have : nextRoot (p * q) a b = a := by unfold nextRoot; rw [if_pos (by simp [hp])]
    have hpa : nextRoot p a b = a := by unfold nextRoot; rw [if_pos hp]
    rw [this, hpa, min_eq_left (S173I_next_ge q a b)]
  by_cases hq : q = 0
  · have : nextRoot (p * q) a b = a := by unfold nextRoot; rw [if_pos (by simp [hq])]
    have hqa : nextRoot q a b = a := by unfold nextRoot; rw [if_pos hq]
    rw [this, hqa, min_eq_right (S173I_next_ge p a b)]
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨cP1, cP2⟩ := S173I_next_char p a b hp
  obtain ⟨cQ1, cQ2⟩ := S173I_next_char q a b hq
  obtain ⟨cR1, cR2⟩ := S173I_next_char (p * q) a b hpq
  apply le_antisymm
  · apply le_min
    · rcases cP1 with h | ⟨h1, h2, h3⟩
      · rw [h]; exact S173I_next_le _ a b hpq
      · exact cR2 _ h1 h2 (by simp [h3])
    · rcases cQ1 with h | ⟨h1, h2, h3⟩
      · rw [h]; exact S173I_next_le _ a b hpq
      · exact cR2 _ h1 h2 (by simp [h3])
  · rcases cR1 with h | ⟨h1, h2, h3⟩
    · rw [h]; exact (min_le_left _ _).trans (S173I_next_le p a b hp)
    · rw [eval_mul] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact (min_le_left _ _).trans (cP2 _ h1 h2 h)
      · exact (min_le_right _ _).trans (cQ2 _ h1 h2 h)

theorem S173I_prev_mul (a b : R) (p q : Polynomial R) :
    prevRoot (p * q) a b = max (prevRoot p a b) (prevRoot q a b) := by
  by_cases hp : p = 0
  · have : prevRoot (p * q) a b = b := by unfold prevRoot; rw [if_pos (by simp [hp])]
    have hpa : prevRoot p a b = b := by unfold prevRoot; rw [if_pos hp]
    rw [this, hpa, max_eq_left (S173I_prev_le q a b)]
  by_cases hq : q = 0
  · have : prevRoot (p * q) a b = b := by unfold prevRoot; rw [if_pos (by simp [hq])]
    have hqa : prevRoot q a b = b := by unfold prevRoot; rw [if_pos hq]
    rw [this, hqa, max_eq_right (S173I_prev_le p a b)]
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨cP1, cP2⟩ := S173I_prev_char p a b hp
  obtain ⟨cQ1, cQ2⟩ := S173I_prev_char q a b hq
  obtain ⟨cR1, cR2⟩ := S173I_prev_char (p * q) a b hpq
  apply le_antisymm
  · rcases cR1 with h | ⟨h1, h2, h3⟩
    · rw [h]; exact (S173I_prev_ge p a b hp).trans (le_max_left _ _)
    · rw [eval_mul] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact (cP2 _ h1 h2 h).trans (le_max_left _ _)
      · exact (cQ2 _ h1 h2 h).trans (le_max_right _ _)
  · apply max_le
    · rcases cP1 with h | ⟨h1, h2, h3⟩
      · rw [h]; exact S173I_prev_ge _ a b hpq
      · exact cR2 _ h1 h2 (by simp [h3])
    · rcases cQ1 with h | ⟨h1, h2, h3⟩
      · rw [h]; exact S173I_prev_ge _ a b hpq
      · exact cR2 _ h1 h2 (by simp [h3])

end S173G

end

end QAlgorithms.Papers.Independent.Dependency50.P27

open Polynomial QAlgorithms.Papers.Independent.Dependency50.P27

theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p q : Polynomial R) :
    ∀ x, x ∈ neighpl (p * q) a b ↔ x ∈ neighpl p a b ∧ x ∈ neighpl q a b := by
  intro x
  simp only [neighpl, Set.mem_Ioo, S173I_prev_mul a b p q, max_lt_iff]
  tauto
