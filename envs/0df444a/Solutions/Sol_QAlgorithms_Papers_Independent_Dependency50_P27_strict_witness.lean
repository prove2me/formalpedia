-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.strict_witness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:23:11.894062+00:00
-- url     : https://prove2.me/submissions/1df18a53-a4d1-43e2-8aac-c5f653d0cff7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27
namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

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

end S173G

end

end QAlgorithms.Papers.Independent.Dependency50.P27

open Polynomial QAlgorithms.Papers.Independent.Dependency50.P27

theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (qs : List (Polynomial R))
    (h : ∃ x : R, ∀ q ∈ qs, 0 < q.eval x) :
    ∃ y : R, (∀ q ∈ qs, 0 < q.eval y) ∧
      ((∀ q ∈ qs, ∀ r : R, q.eval r = 0 → r < y) ∨
       (∀ q ∈ qs, ∀ r : R, q.eval r = 0 → y < r) ∨
       qs.prod.derivative.eval y = 0) := S173G_strict qs h
