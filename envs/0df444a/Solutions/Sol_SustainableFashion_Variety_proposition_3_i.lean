-- Prove2me | solution 1 for SustainableFashion.Variety.proposition_3_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:01:41.636086+00:00
-- url     : https://prove2.me/submissions/8ce05ff1-5f04-4b41-8886-0d7a341e9633

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

set_option autoImplicit false
open SustainableFashion.Variety

noncomputable def ff (P : Params) (m q : ℝ) : ℝ :=
  m * P.k * q + P.k' * ((P.nbar - q) ^ 2 / (2 * P.nbar))

noncomputable def qh (P : Params) (m : ℝ) : ℝ :=
  if m * P.k ≤ P.k' then P.nbar * (1 - m * P.k / P.k') else 0

noncomputable def ffs (P : Params) (m : ℝ) : ℝ := ff P m (qh P m)

noncomputable def Bf (P : Params) (m : ℝ) : ℝ :=
  (P.a + P.γ / 2 - P.γ / (4 * m)) * (P.nbar / 2) - P.β * m

lemma expProfit_eq (P : Params) (m u q : ℝ) :
    expProfit P m u q = Bf P m + P.θ * P.nbar / 2 * u - u ^ 2 / 2 * ff P m q := by
  unfold expProfit Bf ff; ring

lemma qh_mem (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m) :
    0 ≤ qh P m ∧ qh P m ≤ P.nbar := by
  unfold qh
  split_ifs with h
  · have h1 : m * P.k / P.k' ≤ 1 := by rw [div_le_one hk']; exact h
    have h2 : 0 ≤ m * P.k / P.k' := by positivity
    constructor
    · exact mul_nonneg hn.le (by linarith)
    · nlinarith
  · exact ⟨le_refl _, hn.le⟩

lemma ff_ge (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m)
    (q : ℝ) (hq0 : 0 ≤ q) :
    ff P m (qh P m) + P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 ≤ ff P m q := by
  by_cases h : m * P.k ≤ P.k'
  · have e : qh P m = P.nbar * (1 - m * P.k / P.k') := by unfold qh; rw [if_pos h]
    rw [e]
    apply le_of_eq
    unfold ff
    field_simp
    ring
  · have e : qh P m = 0 := by unfold qh; rw [if_neg h]
    rw [e]
    have h' : P.k' < m * P.k := not_le.mp h
    have : ff P m q - (ff P m 0 + P.k' / (2 * P.nbar) * (q - 0) ^ 2) = (m * P.k - P.k') * q := by
      unfold ff
      field_simp
      ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h'.le) hq0]

lemma ffs_case1 (P : Params) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (h : m * P.k ≤ P.k') :
    ffs P m = m * P.k * P.nbar * (2 * P.k' - m * P.k) / (2 * P.k') := by
  unfold ffs qh ff
  rw [if_pos h]
  field_simp
  ring

lemma ffs_case2 (P : Params) (hn : 0 < P.nbar) (m : ℝ) (h : ¬ m * P.k ≤ P.k') :
    ffs P m = P.k' * P.nbar / 2 := by
  unfold ffs qh ff
  rw [if_neg h]
  field_simp
  ring

lemma ffs_pos (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m) :
    0 < ffs P m := by
  by_cases h : m * P.k ≤ P.k'
  · rw [ffs_case1 P hk' hn m h]
    have : 0 < 2 * P.k' - m * P.k := by linarith
    positivity
  · rw [ffs_case2 P hn m h]
    positivity

lemma quad_id (s t u : ℝ) (hs : 0 < s) :
    t * u - u ^ 2 * s / 2 = t ^ 2 / (2 * s) - s / 2 * (u - t / s) ^ 2 := by
  field_simp
  ring

lemma optGiven_iff (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) (u q : ℝ) :
    IsOptimalGiven P m u q ↔ (u = P.θ * P.nbar / (2 * ffs P m) ∧ q = qh P m) := by
  have hs := ffs_pos P hk hk' hn m hm
  have hmem := qh_mem P hk hk' hn m hm
  set s := ffs P m with hsdef
  set t := P.θ * P.nbar / 2 with htdef
  have ht : 0 < t := by positivity
  have hu0 : P.θ * P.nbar / (2 * s) = t / s := by rw [htdef]; field_simp
  rw [hu0]
  have hc : 0 < P.k' / (2 * P.nbar) := by positivity
  constructor
  · rintro ⟨⟨hu, hq0, hq1⟩, hopt⟩
    have h1 := hopt (t / s) (qh P m) (by positivity) hmem.1 hmem.2
    rw [expProfit_eq, expProfit_eq, ← htdef] at h1
    have hge := ff_ge P hk hk' hn m hm q hq0
    have e3 : ff P m (qh P m) = s := rfl
    rw [e3] at hge
    have e1 := quad_id s t u hs
    have e2 : t * (t / s) - (t / s) ^ 2 * s / 2 = t ^ 2 / (2 * s) := by field_simp; ring
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 := by positivity
    have hD : 0 ≤ ff P m q - s := by linarith
    have hprod : 0 ≤ u ^ 2 / 2 * (ff P m q - s) := by positivity
    have key : s / 2 * (u - t / s) ^ 2 + u ^ 2 / 2 * (ff P m q - s) ≤ 0 := by
      rw [e3] at h1
      nlinarith [e1, e2]
    have hA : 0 ≤ s / 2 * (u - t / s) ^ 2 := by positivity
    have hA0 : s / 2 * (u - t / s) ^ 2 = 0 := by linarith
    have hB0 : u ^ 2 / 2 * (ff P m q - s) = 0 := by linarith
    have hus : u = t / s := by
      have : (u - t / s) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hA0 with h | h
        · exact absurd h (by positivity)
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    refine ⟨hus, ?_⟩
    have hupos : 0 < u := by rw [hus]; positivity
    have hDz : ff P m q - s = 0 := by
      rcases mul_eq_zero.mp hB0 with h | h
      · exact absurd h (by positivity)
      · exact h
    have : P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
  · rintro ⟨hu, hq⟩
    subst hu
    subst hq
    refine ⟨⟨by positivity, hmem.1, hmem.2⟩, ?_⟩
    intro u' q' hu' hq0' hq1'
    rw [expProfit_eq, expProfit_eq, ← htdef]
    have hge := ff_ge P hk hk' hn m hm q' hq0'
    have e3 : ff P m (qh P m) = s := rfl
    rw [e3] at hge
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q' - qh P m) ^ 2 := by positivity
    have e1 := quad_id s t u' hs
    have e2 : t * (t / s) - (t / s) ^ 2 * s / 2 = t ^ 2 / (2 * s) := by field_simp; ring
    have hA : 0 ≤ s / 2 * (u' - t / s) ^ 2 := by positivity
    have hprod : 0 ≤ u' ^ 2 / 2 * (ff P m q' - s) := by
      apply mul_nonneg (by positivity); linarith
    rw [e3]
    nlinarith [e1, e2]

noncomputable def Vst (P : Params) (m : ℝ) : ℝ :=
  Bf P m + (P.θ * P.nbar / 2) ^ 2 / (2 * ffs P m)

lemma Vst_attained (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) :
    IsOptimalGiven P m (P.θ * P.nbar / (2 * ffs P m)) (qh P m) ∧
    expProfit P m (P.θ * P.nbar / (2 * ffs P m)) (qh P m) = Vst P m := by
  refine ⟨(optGiven_iff P hk hk' hθ hn m hm _ _).mpr ⟨rfl, rfl⟩, ?_⟩
  have hs := ffs_pos P hk hk' hn m hm
  rw [expProfit_eq]
  have e3 : ff P m (qh P m) = ffs P m := rfl
  rw [e3]
  unfold Vst
  field_simp
  ring

lemma le_Vst (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) (u q : ℝ) (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hq1 : q ≤ P.nbar) :
    expProfit P m u q ≤ Vst P m := by
  obtain ⟨h1, h2⟩ := Vst_attained P hk hk' hθ hn m hm
  rw [← h2]
  exact h1.2 u q hu hq0 hq1

lemma Vst_lt (P : Params) (hP : P.Admissible)
    (hγ : P.γ ≤ 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k)))
    (m : ℝ) (hm : 1 < m) : Vst P m < Vst P 1 := by
  obtain ⟨hk, hkk', hθ, hγ0, hβ, hn⟩ := hP
  have hk' : 0 < P.k' := by linarith
  have hm0 : 0 < m := by linarith
  have h3 : 0 < 2 * P.k' - P.k := by linarith
  have hs1 : ffs P 1 = P.k * P.nbar * (2 * P.k' - P.k) / (2 * P.k') := by
    have := ffs_case1 P hk' hn 1 (by linarith)
    simpa using this
  by_cases h : m * P.k ≤ P.k'
  · have hsm := ffs_case1 P hk' hn m h
    have h2 : 0 < 2 * P.k' - m * P.k := by linarith
    have h2' : 2 * P.k' - m * P.k ≠ 0 := h2.ne'
    have h3' : 2 * P.k' - P.k ≠ 0 := h3.ne'
    have hk0 : P.k ≠ 0 := hk.ne'
    have hk0' : P.k' ≠ 0 := hk'.ne'
    have hm00 : m ≠ 0 := hm0.ne'
    have hΓR : 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k)) ≤
        2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k)) := by
      have e : 2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k)) -
          2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k)) =
          2 * P.θ ^ 2 * (P.k * P.k' * (P.k' - P.k) + (P.k' - m * P.k) * (P.k * (2 * P.k' - P.k))) /
            (P.k * (2 * P.k' - P.k) * P.k' * (2 * P.k' - m * P.k)) := by
        have hd1 : P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k) ≠ 0 := by positivity
        have hd2 : P.k * P.k' * (2 * P.k' - P.k) ≠ 0 := by positivity
        have hd3 : P.k * (2 * P.k' - P.k) * P.k' * (2 * P.k' - m * P.k) ≠ 0 := by positivity
        rw [div_sub_div _ _ hd1 hd2, div_eq_div_iff (mul_ne_zero hd1 hd2) hd3]
        ring
      have hnn : 0 ≤ 2 * P.θ ^ 2 * (P.k * P.k' * (P.k' - P.k) +
          (P.k' - m * P.k) * (P.k * (2 * P.k' - P.k))) /
            (P.k * (2 * P.k' - P.k) * P.k' * (2 * P.k' - m * P.k)) := by
        apply div_nonneg
        · apply mul_nonneg (by positivity)
          apply add_nonneg
          · exact mul_nonneg (mul_nonneg hk.le hk'.le) (by linarith)
          · exact mul_nonneg (by linarith) (mul_nonneg hk.le h3.le)
        · positivity
      linarith
    have hγR := hγ.trans hΓR
    have hR : P.γ - 2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k)) ≤ 0 := by linarith
    have hdiff : Vst P m - Vst P 1 = (m - 1) * (P.nbar / (8 * m) *
        (P.γ - 2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k))) - P.β) := by
      unfold Vst Bf
      rw [hsm, hs1]
      field_simp
      ring
    have hneg : P.nbar / (8 * m) * (P.γ - 2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k))) - P.β < 0 := by
      have : P.nbar / (8 * m) * (P.γ - 2 * P.θ ^ 2 * P.k' * (2 * P.k' - P.k - P.k * m) /
          (P.k * (2 * P.k' - m * P.k) * (2 * P.k' - P.k))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hR
      linarith
    have : Vst P m - Vst P 1 < 0 := by
      rw [hdiff]
      exact mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  · have hsm := ffs_case2 P hn m h
    have h3' : 2 * P.k' - P.k ≠ 0 := h3.ne'
    have hk0 : P.k ≠ 0 := hk.ne'
    have hk0' : P.k' ≠ 0 := hk'.ne'
    have hm00 : m ≠ 0 := hm0.ne'
    have hdiff : Vst P m - Vst P 1 =
        P.nbar / 8 * (P.γ - 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k)))
          - P.nbar * P.γ / (8 * m) - P.β * (m - 1) := by
      unfold Vst Bf
      rw [hsm, hs1]
      field_simp
      ring
    have h1 : P.nbar / 8 * (P.γ - 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k)))
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h2 : 0 < P.nbar * P.γ / (8 * m) := by positivity
    have h3 : 0 < P.β * (m - 1) := mul_pos hβ (by linarith)
    linarith

theorem solution (P : Params) (hP : P.Admissible)
    (hγ : P.γ ≤ 2 * (P.k' - P.k) ^ 2 * P.θ ^ 2 / (P.k * P.k' * (2 * P.k' - P.k))) :
    (∃ u q, IsOptimal P 1 u q) ∧ ∀ m u q, IsOptimal P m u q → m = 1 := by
  have hP' := hP
  obtain ⟨hk, hkk', hθ, hγ0, hβ, hn⟩ := hP'
  have hk' : 0 < P.k' := by linarith
  have hlt := Vst_lt P hP hγ
  obtain ⟨hopt1, hval⟩ := Vst_attained P hk hk' hθ hn 1 one_pos
  have hopt : IsOptimal P 1 (P.θ * P.nbar / (2 * ffs P 1)) (qh P 1) := by
    refine ⟨⟨le_refl 1, hopt1.1.1, hopt1.1.2.1, hopt1.1.2.2⟩, ?_⟩
    rintro m' u' q' ⟨hm', hu', hq0', hq1'⟩
    rw [hval]
    calc expProfit P m' u' q' ≤ Vst P m' :=
          le_Vst P hk hk' hθ hn m' (by linarith) u' q' hu' hq0' hq1'
      _ ≤ Vst P 1 := by
          rcases hm'.eq_or_lt with h | h
          · rw [← h]
          · exact (hlt m' h).le
  refine ⟨⟨_, _, hopt⟩, ?_⟩
  rintro m u q ⟨⟨hm, hu, hq0, hq1⟩, hmax⟩
  by_contra hne
  have h1m : 1 < m := lt_of_le_of_ne hm (Ne.symm hne)
  have h1 := hmax 1 _ _ hopt.1
  have h2 := le_Vst P hk hk' hθ hn m (by linarith) u q hu hq0 hq1
  have h3 := hlt m h1m
  have h4 : expProfit P 1 (P.θ * P.nbar / (2 * ffs P 1)) (qh P 1) = Vst P 1 := hval
  linarith
