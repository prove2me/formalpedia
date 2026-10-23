-- Prove2me | solution 1 for SellVsPPU.Duopoly.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T03:08:27.809352+00:00
-- url     : https://prove2.me/submissions/932857ce-c805-4928-a626-ed535657b70b

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

set_option autoImplicit false

open MeasureTheory

namespace SVPPUAux
open SellVsPPU.Duopoly

lemma vol_Icc (x y : ℝ) : (volume (Set.Icc x y)).toReal = max (y - x) 0 := by
  rw [Real.volume_Icc, ENNReal.toReal_ofReal']

lemma int_Icc (m : ℝ) : (∫ q in Set.Icc (0:ℝ) m, q) = (max m 0) ^ 2 / 2 := by
  rcases le_or_gt 0 m with h | h
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h, integral_id,
      max_eq_left h]
    ring
  · rw [Set.Icc_eq_empty (by linarith), Measure.restrict_empty, integral_zero_measure,
      max_eq_right h.le]
    ring

lemma sellSet_pos (P : Params) (ps pu : ℝ) (hpu : 0 < pu) (hpa : pu ≤ P.a) :
    sellSet P ps pu = Set.Icc (max 0 (ps / pu)) P.qm := by
  ext q
  simp only [sellSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, max_le_iff, div_le_iff₀ hpu]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨⟨h0, by nlinarith⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    exact ⟨⟨h0, h1⟩, by nlinarith, by nlinarith⟩

lemma ppuSet_pos (P : Params) (ps pu : ℝ) (hpu : 0 < pu) (hpa : pu ≤ P.a) :
    ppuSet P ps pu = Set.Icc 0 (min P.qm (ps / pu)) := by
  ext q
  simp only [ppuSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff, le_div_iff₀ hpu]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    exact ⟨h0, h1, by nlinarith⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, h1⟩, by nlinarith, by nlinarith⟩

lemma ppuSet_nonpos (P : Params) (ps pu : ℝ) (hpu : pu ≤ 0) (hps : 0 ≤ ps) (ha : 0 < P.a) :
    ppuSet P ps pu = Set.Icc 0 P.qm := by
  ext q
  simp only [ppuSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨h, -, -⟩
    exact h
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0, h1⟩, by nlinarith, by nlinarith⟩

lemma sellSet_sub (P : Params) (ps pu : ℝ) (hpu : pu ≤ 0) (hps : ps < 0) (ha : 0 < P.a) :
    Set.Icc 0 (min P.qm (ps / (pu - 1))) ⊆ sellSet P ps pu := by
  intro q hq
  simp only [Set.mem_Icc, le_min_iff] at hq
  obtain ⟨h0, h1, h2⟩ := hq
  have hneg : pu - 1 < 0 := by linarith
  rw [le_div_iff_of_neg hneg] at h2
  simp only [sellSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc]
  exact ⟨⟨h0, h1⟩, by nlinarith, by nlinarith⟩

lemma sellSet_empty (P : Params) (ps pu : ℝ) (ha : 0 < P.a) (h : P.a * P.qm < ps) :
    sellSet P ps pu = ∅ := by
  ext q
  simp only [sellSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h0, h1⟩, h2, -⟩
  nlinarith

lemma profitS_pos (P : Params) (ps pu : ℝ) (hpu : 0 < pu) (hpa : pu ≤ P.a) :
    profitS P ps pu = (ps - P.c) * max (P.qm - max 0 (ps / pu)) 0 / P.qm := by
  rw [profitS, sellSet_pos P ps pu hpu hpa, vol_Icc]

lemma profitU_pos (P : Params) (ps pu : ℝ) (hpu : 0 < pu) (hpa : pu ≤ P.a) :
    profitU P ps pu = (pu - cu P) * ((max (min P.qm (ps / pu)) 0) ^ 2 / 2) / P.qm := by
  rw [profitU, ppuSet_pos P ps pu hpu hpa, int_Icc]

lemma seller_bound (qm c pu x : ℝ) (hqm : 0 < qm) (hc : 0 ≤ c) (hpu : 0 < pu)
    (hcp : c ≤ pu * qm) :
    (x - c) * max (qm - max 0 (x / pu)) 0 ≤ (pu * qm - c) ^ 2 / (4 * pu) := by
  have hR : 0 ≤ (pu * qm - c) ^ 2 / (4 * pu) := by positivity
  rcases le_or_gt x 0 with hx | hx
  · have : x / pu ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hpu.le
    rw [max_eq_left this, sub_zero, max_eq_left hqm.le]
    nlinarith
  rcases le_or_gt (pu * qm) x with hx2 | hx2
  · have : qm ≤ x / pu := by rw [le_div_iff₀ hpu]; linarith
    rw [max_eq_right (by linarith : 0 ≤ x / pu), max_eq_right (by linarith : qm - x / pu ≤ 0),
      mul_zero]
    exact hR
  · have hy0 : 0 < x / pu := div_pos hx hpu
    have hy1 : x / pu < qm := by rw [div_lt_iff₀ hpu]; linarith
    have hxy : x = x / pu * pu := by field_simp
    rw [max_eq_right hy0.le, max_eq_left (by linarith : 0 ≤ qm - x / pu),
      le_div_iff₀ (by positivity)]
    generalize x / pu = y at hxy hy0 hy1 ⊢
    subst hxy
    nlinarith [sq_nonneg (2 * pu * y - pu * qm - c)]

lemma seller_unique (qm c pu x : ℝ) (hqm : 0 < qm) (hc : 0 ≤ c) (hpu : 0 < pu)
    (hcp : c < pu * qm)
    (hge : (pu * qm - c) ^ 2 / (4 * pu) ≤ (x - c) * max (qm - max 0 (x / pu)) 0) :
    x = (pu * qm + c) / 2 := by
  have hR : 0 < (pu * qm - c) ^ 2 / (4 * pu) := by
    have : 0 < pu * qm - c := by linarith
    positivity
  rcases le_or_gt x 0 with hx | hx
  · have : x / pu ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hpu.le
    rw [max_eq_left this, sub_zero, max_eq_left hqm.le] at hge
    nlinarith
  rcases le_or_gt (pu * qm) x with hx2 | hx2
  · have : qm ≤ x / pu := by rw [le_div_iff₀ hpu]; linarith
    rw [max_eq_right (by linarith : 0 ≤ x / pu), max_eq_right (by linarith : qm - x / pu ≤ 0),
      mul_zero] at hge
    linarith
  · have hy0 : 0 < x / pu := div_pos hx hpu
    have hy1 : x / pu < qm := by rw [div_lt_iff₀ hpu]; linarith
    have hxy : x = x / pu * pu := by field_simp
    rw [max_eq_right hy0.le, max_eq_left (by linarith : 0 ≤ qm - x / pu),
      div_le_iff₀ (by positivity)] at hge
    generalize x / pu = y at hxy hy0 hy1 hge
    subst hxy
    have h2 : (2 * pu * y - pu * qm - c) ^ 2 ≤ 0 := by nlinarith
    have h3 : 2 * pu * y - pu * qm - c = 0 := by
      have := sq_nonneg (2 * pu * y - pu * qm - c)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 this)
    linarith

lemma seller_value (qm c pu : ℝ) (hqm : 0 < qm) (hc : 0 ≤ c) (hpu : 0 < pu)
    (hcp : c ≤ pu * qm) :
    ((pu * qm + c) / 2 - c) * max (qm - max 0 ((pu * qm + c) / 2 / pu)) 0
      = (pu * qm - c) ^ 2 / (4 * pu) := by
  have h1 : 0 ≤ (pu * qm + c) / 2 / pu := by positivity
  have h2 : 0 ≤ qm - (pu * qm + c) / 2 / pu := by
    rw [sub_nonneg, div_le_iff₀ hpu]; linarith
  rw [max_eq_right h1, max_eq_left h2]
  field_simp
  ring

lemma m_bounds (qm s p : ℝ) (hqm : 0 < qm) (hsp : 0 ≤ s / p) :
    0 ≤ max (min qm (s / p)) 0 ∧ max (min qm (s / p)) 0 ≤ s / p :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hsp⟩

lemma ppu_bound_gen (qm k s p C : ℝ) (hqm : 0 < qm) (hs : 0 < s) (hp : 0 < p)
    (hC0 : 0 ≤ C) (hC : (p - k) * (s / p) ^ 2 ≤ C) :
    (p - k) * (max (min qm (s / p)) 0) ^ 2 ≤ C := by
  obtain ⟨h0, h1⟩ := m_bounds qm s p hqm (div_pos hs hp).le
  rcases le_or_gt p k with hpk | hpk
  · have : (p - k) * (max (min qm (s / p)) 0) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  · calc (p - k) * (max (min qm (s / p)) 0) ^ 2 ≤ (p - k) * (s / p) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact pow_le_pow_left₀ h0 h1 2
      _ ≤ C := hC

lemma ppu_case1 (k s p : ℝ) (hk : 0 < k) (hp : 0 < p) :
    (p - k) * (s / p) ^ 2 ≤ s ^ 2 / (4 * k) := by
  rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg (p - 2 * k))]

lemma ppu_case2 (a k s p : ℝ) (hk : 0 < k) (hp : 0 < p) (hpa : p ≤ a) (ha2 : a ≤ 2 * k) :
    (p - k) * (s / p) ^ 2 ≤ (a - k) * (s / a) ^ 2 := by
  have ha : 0 < a := by linarith
  rw [div_pow, div_pow, mul_div_assoc', mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ k * (a + p) - a * p := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hpa) h1) (sq_nonneg s)]

lemma ratio_lt (k s p q : ℝ) (hs : 0 < s) (hp : 0 < p) (hq : 0 < q)
    (h : 0 < (q - p) * (k * (p + q) - p * q)) :
    (p - k) * (s / p) ^ 2 < (q - k) * (s / q) ^ 2 := by
  rw [div_pow, div_pow, mul_div_assoc', mul_div_assoc',
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : (p - k) * q ^ 2 < (q - k) * p ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right key (pow_pos hs 2)]

lemma cu_pos (P : Params) (hP : P.Admissible) : 0 < cu P := by
  obtain ⟨ha, hqm, hc, hd, hcu⟩ := hP
  unfold cu; positivity

lemma cu_mul (P : Params) (hP : P.Admissible) : cu P * P.qm = P.c + P.delta * P.qm := by
  obtain ⟨ha, hqm, hc, hd, hcu⟩ := hP
  unfold cu; field_simp

lemma isEq_of (P : Params) (hP : P.Admissible) (pu0 : ℝ) (hpu : 0 < pu0) (hpa : pu0 ≤ P.a)
    (hcp : P.c ≤ pu0 * P.qm) (hku : cu P ≤ pu0)
    (hppu : ∀ p, 0 < p → p ≤ P.a →
      (p - cu P) * (max (min P.qm ((pu0 * P.qm + P.c) / 2 / p)) 0) ^ 2 ≤
      (pu0 - cu P) * (max (min P.qm ((pu0 * P.qm + P.c) / 2 / pu0)) 0) ^ 2) :
    IsPriceEq P ((pu0 * P.qm + P.c) / 2) pu0 := by
  have hk := cu_pos P hP
  obtain ⟨ha, hqm, hc, hd, hcu⟩ := hP
  refine ⟨hpa, ?_, ?_⟩
  · intro x
    rw [profitS_pos P _ _ hpu hpa, profitS_pos P _ _ hpu hpa,
      seller_value _ _ _ hqm hc.le hpu hcp]
    exact div_le_div_of_nonneg_right (seller_bound _ _ _ x hqm hc.le hpu hcp) hqm.le
  · intro p hp
    have hU0 : 0 ≤ profitU P ((pu0 * P.qm + P.c) / 2) pu0 := by
      rw [profitU_pos P _ _ hpu hpa]
      have : 0 ≤ pu0 - cu P := by linarith
      exact div_nonneg (mul_nonneg this (by positivity)) hqm.le
    rcases le_or_gt p 0 with hp0 | hp0
    · rw [profitU, ppuSet_nonpos P _ _ hp0 (by positivity) ha, int_Icc, max_eq_left hqm.le]
      have : (p - cu P) * (P.qm ^ 2 / 2) / P.qm ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) hqm.le
      linarith
    · rw [profitU_pos P _ _ hp0 hp, profitU_pos P _ _ hpu hpa]
      apply div_le_div_of_nonneg_right _ hqm.le
      have := hppu p hp0 hp
      linarith

lemma eq_unique (P : Params) (hP : P.Admissible) (hnd : P.c < P.a * P.qm) (ps pu : ℝ)
    (h : IsPriceEq P ps pu) :
    0 < pu ∧ P.c < pu * P.qm ∧ ps = (pu * P.qm + P.c) / 2 ∧
    ((2 * cu P ≤ P.a ∧ pu = 2 * cu P) ∨ (P.a < 2 * cu P ∧ pu = P.a)) := by
  have hk := cu_pos P hP
  obtain ⟨ha, hqm, hc, hd, hcu⟩ := hP
  obtain ⟨hpa, hS, hU⟩ := h
  have hka : cu P ≤ P.a := hcu
  have hkc : P.c / P.qm ≤ cu P := by unfold cu; linarith
  have hS0 : 0 ≤ profitS P ps pu := by
    have h0 : profitS P P.c pu = 0 := by simp [profitS]
    linarith [hS P.c]
  have hUa := hU P.a le_rfl
  -- Step A: pu > 0
  have hpu : 0 < pu := by
    by_contra hneg
    push Not at hneg
    rcases le_or_gt 0 ps with hps | hps
    · have hUa0 : 0 ≤ profitU P ps P.a := by
        rw [profitU_pos P _ _ ha le_rfl]
        exact div_nonneg (mul_nonneg (by linarith) (by positivity)) hqm.le
      have hUpu : profitU P ps pu = (pu - cu P) * (P.qm ^ 2 / 2) / P.qm := by
        rw [profitU, ppuSet_nonpos P _ _ hneg hps ha, int_Icc, max_eq_left hqm.le]
      rw [hUpu] at hUa
      have : (pu - cu P) * (P.qm ^ 2 / 2) / P.qm < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by positivity)) hqm
      linarith
    · have hsub := sellSet_sub P ps pu hneg hps ha
      have hε : 0 < min P.qm (ps / (pu - 1)) :=
        lt_min hqm (div_pos_of_neg_of_neg hps (by linarith))
      have hfin : volume (sellSet P ps pu) ≠ ⊤ := by
        apply ne_top_of_le_ne_top (b := volume (Set.Icc (0:ℝ) P.qm))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        apply measure_mono
        intro q hq
        exact hq.1
      have hv : min P.qm (ps / (pu - 1)) ≤ (volume (sellSet P ps pu)).toReal := by
        have := ENNReal.toReal_mono hfin (measure_mono hsub)
        rw [vol_Icc, sub_zero, max_eq_left hε.le] at this
        exact this
      have : profitS P ps pu < 0 := by
        rw [profitS]
        exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) hqm
      linarith
  -- Step B: pu * qm > c
  have hcp : P.c < pu * P.qm := by
    by_contra hle
    push Not at hle
    have hpuc : pu ≤ P.c / P.qm := by rw [le_div_iff₀ hqm]; exact hle
    have hpuk : pu ≤ cu P := by linarith
    rw [profitS_pos P _ _ hpu hpa] at hS0
    have ht : P.qm ≤ ps / pu := by
      by_contra hlt
      push Not at hlt
      have h1 : ps < P.c := by
        have := (div_lt_iff₀ hpu).mp hlt
        linarith
      have h2 : 0 < max (P.qm - max 0 (ps / pu)) 0 := by
        apply lt_max_of_lt_left
        have : max 0 (ps / pu) < P.qm := max_lt hqm hlt
        linarith
      have : (ps - P.c) * max (P.qm - max 0 (ps / pu)) 0 / P.qm < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) h2) hqm
      linarith
    have hps : 0 < ps := by
      have := (le_div_iff₀ hpu).mp ht
      nlinarith
    rw [profitU_pos P _ _ hpu hpa, min_eq_left ht, max_eq_left hqm.le,
      profitU_pos P _ _ ha le_rfl] at hUa
    have hm : 0 < max (min P.qm (ps / P.a)) 0 :=
      lt_max_of_lt_left (lt_min hqm (div_pos hps ha))
    rcases lt_or_eq_of_le hpuk with hlt | heq
    · have : (pu - cu P) * (P.qm ^ 2 / 2) / P.qm < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by positivity)) hqm
      have : 0 ≤ (P.a - cu P) * ((max (min P.qm (ps / P.a)) 0) ^ 2 / 2) / P.qm :=
        div_nonneg (mul_nonneg (by linarith) (by positivity)) hqm.le
      linarith
    · have hka' : cu P < P.a := by
        have : P.c / P.qm < P.a := by rw [div_lt_iff₀ hqm]; linarith
        linarith
      have : 0 < (P.a - cu P) * ((max (min P.qm (ps / P.a)) 0) ^ 2 / 2) / P.qm :=
        div_pos (mul_pos (by linarith) (by positivity)) hqm
      rw [heq, sub_self, zero_mul, zero_div] at hUa
      linarith
  -- Step C: seller best response
  have hps : ps = (pu * P.qm + P.c) / 2 := by
    apply seller_unique P.qm P.c pu ps hqm hc.le hpu hcp
    have h1 := hS ((pu * P.qm + P.c) / 2)
    rw [profitS_pos P _ _ hpu hpa, profitS_pos P _ _ hpu hpa,
      seller_value _ _ _ hqm hc.le hpu hcp.le] at h1
    exact (div_le_div_iff_of_pos_right hqm).mp h1
  refine ⟨hpu, hcp, hps, ?_⟩
  -- Step D: service best response
  have hps0 : 0 < ps := by rw [hps]; positivity
  have ht0 : 0 < ps / pu := div_pos hps0 hpu
  have htq : ps / pu < P.qm := by
    rw [div_lt_iff₀ hpu, hps]; linarith
  have hpsq : ps < P.qm * pu := (div_lt_iff₀ hpu).mp htq
  have hUpu : profitU P ps pu = (pu - cu P) * ((ps / pu) ^ 2 / 2) / P.qm := by
    rw [profitU_pos P _ _ hpu hpa, min_eq_right htq.le, max_eq_left ht0.le]
  have hdev : ∀ p', 0 < p' → p' ≤ P.a → ps / p' ≤ P.qm →
      profitU P ps p' = (p' - cu P) * ((ps / p') ^ 2 / 2) / P.qm := by
    intro p' hp' hpa' hq'
    rw [profitU_pos P _ _ hp' hpa', min_eq_right hq', max_eq_left (div_pos hps0 hp').le]
  have hle2 : pu ≤ 2 * cu P := by
    by_contra hgt
    push Not at hgt
    obtain ⟨p', hp'⟩ : ∃ p', p' = max (2 * cu P) (ps / P.qm) := ⟨_, rfl⟩
    have hp'pu : p' < pu := by
      rw [hp']
      exact max_lt hgt (by rw [div_lt_iff₀ hqm]; linarith)
    have h2k : 2 * cu P ≤ p' := by rw [hp']; exact le_max_left _ _
    have hp'0 : 0 < p' := by linarith
    have hq' : ps / p' ≤ P.qm := by
      have := le_max_right (2 * cu P) (ps / P.qm)
      rw [← hp', div_le_iff₀ hqm] at this
      rw [div_le_iff₀ hp'0]
      linarith
    have f1 : p' - pu < 0 := by linarith
    have f2 : cu P * (pu + p') - pu * p' < 0 := by
      nlinarith [mul_le_mul_of_nonneg_left h2k hpu.le, mul_lt_mul_of_pos_left hp'pu hk]
    have himp := ratio_lt (cu P) ps pu p' hps0 hpu hp'0 (mul_pos_of_neg_of_neg f1 f2)
    have := hU p' (by linarith)
    rw [hdev p' hp'0 (by linarith) hq', hUpu] at this
    have := (div_le_div_iff_of_pos_right hqm).mp this
    linarith
  rcases lt_or_eq_of_le hle2 with hlt2 | heq2
  · have hpa_eq : pu = P.a := by
      by_contra hne
      have hlta : pu < P.a := lt_of_le_of_ne hpa hne
      obtain ⟨p', hp'⟩ : ∃ p', p' = min P.a (2 * cu P) := ⟨_, rfl⟩
      have hpup' : pu < p' := by rw [hp']; exact lt_min hlta hlt2
      have hp'0 : 0 < p' := by linarith
      have hp'a : p' ≤ P.a := by rw [hp']; exact min_le_left _ _
      have hp'2 : p' ≤ 2 * cu P := by rw [hp']; exact min_le_right _ _
      have hq' : ps / p' ≤ P.qm := by
        rw [div_le_iff₀ hp'0]
        nlinarith [mul_le_mul_of_nonneg_left hpup'.le hqm.le]
      have f2 : 0 < cu P * (pu + p') - pu * p' := by
        nlinarith [mul_le_mul_of_nonneg_left hp'2 hpu.le, mul_lt_mul_of_pos_left hpup' hk]
      have himp := ratio_lt (cu P) ps pu p' hps0 hpu hp'0 (mul_pos (by linarith) f2)
      have := hU p' hp'a
      rw [hdev p' hp'0 hp'a hq', hUpu] at this
      have := (div_le_div_iff_of_pos_right hqm).mp this
      linarith
    exact Or.inr ⟨by linarith, hpa_eq⟩
  · exact Or.inl ⟨by linarith, heq2⟩

lemma gen_iff (qm c u k : ℝ) (hu : 0 < u) :
    (u * qm - c) ^ 2 / (4 * u) ≤ (u - k) * (((u * qm + c) / 2 / u) ^ 2 / 2) ↔
      2 * u * (u * qm - c) ^ 2 ≤ (u - k) * (u * qm + c) ^ 2 := by
  have e : (u - k) * (((u * qm + c) / 2 / u) ^ 2 / 2) = (u - k) * (u * qm + c) ^ 2 / (8 * u ^ 2) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have e2 : (u * qm - c) ^ 2 * (8 * u ^ 2) = (4 * u) * (2 * u * (u * qm - c) ^ 2) := by ring
  have e3 : (u - k) * (u * qm + c) ^ 2 * (4 * u) = (4 * u) * ((u - k) * (u * qm + c) ^ 2) := by
    ring
  rw [e2, e3]
  exact ⟨fun h => le_of_mul_le_mul_left h (by positivity),
    fun h => mul_le_mul_of_nonneg_left h (by positivity)⟩

lemma case1_iff (a qm c d k u : ℝ) (ha : 0 < a) (hqm : 0 < qm) (hc : 0 < c) (hd : 0 ≤ d)
    (hk : 0 < k) (hkm : k * qm = c + d * qm) (h2k : 2 * k ≤ a) (hu : u = 2 * k) :
    2 * u * (u * qm - c) ^ 2 ≤ (u - k) * (u * qm + c) ^ 2 ↔ d ≤ deltaBar a qm c := by
  subst hu
  have hX : 2 * k * qm - c = c + 2 * d * qm := by linarith
  have hY : 2 * k * qm + c = 3 * c + 2 * d * qm := by linarith
  rw [hX, hY]
  have hp : 0 < k * (5 * c + 6 * d * qm) := by positivity
  have key : 2 * (2 * k) * (c + 2 * d * qm) ^ 2 - (2 * k - k) * (3 * c + 2 * d * qm) ^ 2
      = k * (5 * c + 6 * d * qm) * (2 * d * qm - c) := by ring
  have hiff : 2 * (2 * k) * (c + 2 * d * qm) ^ 2 ≤ (2 * k - k) * (3 * c + 2 * d * qm) ^ 2 ↔
      2 * d * qm ≤ c := by
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      have := mul_pos hp (by linarith : 0 < 2 * d * qm - c)
      linarith
    · intro h
      have := mul_le_mul_of_nonneg_left (by linarith : 2 * d * qm - c ≤ 0) hp.le
      linarith
  rw [hiff]
  have hkq : k * qm ≤ a / 2 * qm := mul_le_mul_of_nonneg_right (by linarith) hqm.le
  unfold deltaBar
  split_ifs with h3
  · rw [le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  · push Not at h3
    have hcq : c / qm = k - d := by
      rw [div_eq_iff hqm.ne']
      linarith
    have hca : c ≤ a * qm := by nlinarith
    obtain ⟨r, hr⟩ : ∃ r, r = (a * qm - c) / (a * qm + c) := ⟨_, rfl⟩
    have hY0 : 0 < a * qm + c := by positivity
    have hrY : a * qm - c = r * (a * qm + c) := by rw [hr]; field_simp
    have hr0 : 0 ≤ r := by rw [hr]; exact div_nonneg (by linarith) hY0.le
    have hr1 : r ≤ 1 / 2 := by
      by_contra hgt
      push Not at hgt
      nlinarith
    rw [hcq, ← hr]
    constructor
    · intro _
      nlinarith
    · intro _
      have : a * qm < 3 * c := by linarith
      nlinarith

lemma case2_iff (a qm c d k : ℝ) (ha : 0 < a) (hqm : 0 < qm) (hc : 0 < c) (hd : 0 ≤ d)
    (hk : 0 < k) (hkm : k * qm = c + d * qm) (ha2 : a < 2 * k) (hca : c ≤ a * qm) :
    2 * a * (a * qm - c) ^ 2 ≤ (a - k) * (a * qm + c) ^ 2 ↔ d ≤ deltaBar a qm c := by
  obtain ⟨r, hr⟩ : ∃ r, r = (a * qm - c) / (a * qm + c) := ⟨_, rfl⟩
  have hY0 : 0 < a * qm + c := by positivity
  have hrY : a * qm - c = r * (a * qm + c) := by rw [hr]; field_simp
  have hcq : c / qm = k - d := by
    rw [div_eq_iff hqm.ne']
    linarith
  have hiff : 2 * a * (a * qm - c) ^ 2 ≤ (a - k) * (a * qm + c) ^ 2 ↔ 2 * a * r ^ 2 ≤ a - k := by
    rw [hrY]
    have e : 2 * a * (r * (a * qm + c)) ^ 2 = (2 * a * r ^ 2) * (a * qm + c) ^ 2 := by ring
    rw [e]
    exact ⟨fun h => le_of_mul_le_mul_right h (by positivity),
      fun h => mul_le_mul_of_nonneg_right h (by positivity)⟩
  rw [hiff]
  have hkq : a / 2 * qm < k * qm := mul_lt_mul_of_pos_right (by linarith) hqm
  unfold deltaBar
  split_ifs with h3
  · have hr1 : 1 / 2 ≤ r := by
      by_contra hlt
      push Not at hlt
      nlinarith
    apply iff_of_false
    · intro h
      nlinarith
    · rw [le_div_iff₀ (by positivity)]
      intro h
      nlinarith
  · rw [hcq, ← hr]
    constructor <;> intro h <;> linarith

theorem main (P : Params) (hP : P.Admissible) :
    (∃ ps pu, IsPriceEq P ps pu) ∧
    ∀ ps pu, IsPriceEq P ps pu →
      (profitS P ps pu ≤ profitU P ps pu ↔ P.delta ≤ deltaBar P.a P.qm P.c) := by
  have hk := cu_pos P hP
  have hkm := cu_mul P hP
  have ⟨ha, hqm, hc, hd, hcu⟩ := hP
  have hka : cu P ≤ P.a := hcu
  have hca : P.c ≤ P.a * P.qm := by
    have : P.c / P.qm ≤ P.a := by linarith
    exact (div_le_iff₀ hqm).mp this
  have hck : P.c ≤ cu P * P.qm := by rw [hkm]; nlinarith
  constructor
  · rcases le_or_gt (2 * cu P) P.a with h1 | h2
    · refine ⟨_, _, isEq_of P hP (2 * cu P) (by linarith) h1 (by nlinarith) (by linarith) ?_⟩
      intro p hp hpa
      have hs : 0 < (2 * cu P * P.qm + P.c) / 2 := by positivity
      have hq : (2 * cu P * P.qm + P.c) / 2 / (2 * cu P) ≤ P.qm := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      rw [min_eq_right hq, max_eq_left (div_pos hs (by linarith : (0:ℝ) < 2 * cu P)).le]
      apply ppu_bound_gen _ _ _ _ _ hqm hs hp (mul_nonneg (by linarith) (by positivity))
      calc (p - cu P) * ((2 * cu P * P.qm + P.c) / 2 / p) ^ 2
          ≤ ((2 * cu P * P.qm + P.c) / 2) ^ 2 / (4 * cu P) := ppu_case1 _ _ _ hk hp
        _ = _ := by field_simp; ring
    · refine ⟨_, _, isEq_of P hP P.a ha le_rfl hca hka ?_⟩
      intro p hp hpa
      have hs : 0 < (P.a * P.qm + P.c) / 2 := by positivity
      have hq : (P.a * P.qm + P.c) / 2 / P.a ≤ P.qm := by
        rw [div_le_iff₀ ha]
        nlinarith
      rw [min_eq_right hq, max_eq_left (div_pos hs ha).le]
      exact ppu_bound_gen _ _ _ _ _ hqm hs hp (mul_nonneg (by linarith) (by positivity))
        (ppu_case2 _ _ _ _ hk hp hpa h2.le)
  · intro ps pu h
    rcases lt_or_eq_of_le hca with hnd | hdeg
    · obtain ⟨hpu, hcp, hps, hcase⟩ := eq_unique P hP hnd ps pu h
      have hpa := h.1
      have hSv : profitS P ps pu = (pu * P.qm - P.c) ^ 2 / (4 * pu) / P.qm := by
        rw [profitS_pos P _ _ hpu hpa, hps, seller_value _ _ _ hqm hc.le hpu hcp.le]
      have htq : (pu * P.qm + P.c) / 2 / pu ≤ P.qm := by
        rw [div_le_iff₀ hpu]
        linarith
      have hUv : profitU P ps pu = (pu - cu P) * (((pu * P.qm + P.c) / 2 / pu) ^ 2 / 2) / P.qm := by
        rw [profitU_pos P _ _ hpu hpa, hps, min_eq_right htq, max_eq_left (by positivity)]
      rw [hSv, hUv, div_le_div_iff_of_pos_right hqm, gen_iff _ _ _ _ hpu]
      rcases hcase with ⟨h1, h1'⟩ | ⟨h2, h2'⟩
      · exact case1_iff P.a P.qm P.c P.delta (cu P) pu ha hqm hc hd hk hkm h1 h1'
      · rw [h2']
        exact case2_iff P.a P.qm P.c P.delta (cu P) ha hqm hc hd hk hkm h2 hca
    · have hcq : P.c / P.qm = P.a := by rw [hdeg]; field_simp
      have hd0 : P.delta = 0 := by linarith
      have h3 : ¬ P.c ≤ P.a * P.qm / 3 := by
        rw [hdeg]
        have : 0 < P.a * P.qm := by positivity
        linarith
      have hdb : deltaBar P.a P.qm P.c = 0 := by
        unfold deltaBar
        rw [if_neg h3, hcq, hdeg, sub_self, sub_self, zero_div]
        ring
      refine iff_of_true ?_ (by rw [hdb, hd0])
      have hUa0 : 0 ≤ profitU P ps P.a := by
        rw [profitU_pos P _ _ ha le_rfl]
        exact div_nonneg (mul_nonneg (by linarith) (by positivity)) hqm.le
      have hUa := h.2.2 P.a le_rfl
      have hS0 : profitS P ps pu ≤ 0 := by
        rcases le_or_gt ps P.c with hle | hgt
        · rw [profitS]
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg) hqm.le
        · rw [profitS, sellSet_empty P ps pu ha (by linarith), measure_empty,
            ENNReal.toReal_zero, mul_zero, zero_div]
      linarith

end SVPPUAux

open SellVsPPU.Duopoly in
theorem solution (P : Params) (hP : P.Admissible) :
    (∃ ps pu, IsPriceEq P ps pu) ∧
    ∀ ps pu, IsPriceEq P ps pu →
      (profitS P ps pu ≤ profitU P ps pu ↔
        P.delta ≤ deltaBar P.a P.qm P.c) := by
  exact SVPPUAux.main P hP
