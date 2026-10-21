-- Prove2me | solution 1 for SustainableFashion.Variety.qhat_optimal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:55:17.157646+00:00
-- url     : https://prove2.me/submissions/ff2edc1e-93c5-4c87-9194-68070a65c942

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

theorem solution (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hn : 0 < P.nbar) (m u : ℝ) (hm : 1 ≤ m) (hu : 0 < u)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ P.nbar) :
    (∀ q', 0 ≤ q' → q' ≤ P.nbar → expProfit P m u q' ≤ expProfit P m u q) ↔
      q = (if m * P.k ≤ P.k' then P.nbar * (1 - m * P.k / P.k') else 0) := by
  have hm0 : 0 < m := by linarith
  have hk' : 0 < P.k' := by linarith
  have hmem := qh_mem P hk hk' hn m hm0
  have hc : 0 < P.k' / (2 * P.nbar) := by positivity
  show _ ↔ q = qh P m
  constructor
  · intro H
    have h1 := H (qh P m) hmem.1 hmem.2
    rw [expProfit_eq, expProfit_eq] at h1
    have hge := ff_ge P hk hk' hn m hm0 q hq0
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 := by positivity
    have hu2 : 0 < u ^ 2 / 2 := by positivity
    have h2 : ff P m q ≤ ff P m (qh P m) := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_lt_mul_of_pos_left hcon hu2]
    have : P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
  · intro hq' q' hq0' hq1'
    subst hq'
    rw [expProfit_eq, expProfit_eq]
    have hge := ff_ge P hk hk' hn m hm0 q' hq0'
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q' - qh P m) ^ 2 := by positivity
    have hu2 : 0 < u ^ 2 / 2 := by positivity
    have : ff P m (qh P m) ≤ ff P m q' := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hu2.le]
