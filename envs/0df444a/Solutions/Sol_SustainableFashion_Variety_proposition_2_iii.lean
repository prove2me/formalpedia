-- Prove2me | solution 1 for SustainableFashion.Variety.proposition_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:58:38.648346+00:00
-- url     : https://prove2.me/submissions/c43b80f5-cdb1-4af1-9c2d-c6112b6972d9

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

lemma mono_u (P₁ P₂ : Params) (hθ : P₁.θ = P₂.θ) (hn : P₁.nbar = P₂.nbar)
    (hk₁ : 0 < P₁.k) (hk₁' : 0 < P₁.k') (hk₂ : 0 < P₂.k) (hk₂' : 0 < P₂.k')
    (hθ0 : 0 < P₁.θ) (hn0 : 0 < P₁.nbar) (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hff : ∀ q, 0 ≤ q → ff P₁ m₁ q ≤ ff P₂ m₂ q) (u₁ q₁ u₂ q₂ : ℝ)
    (h₁ : IsOptimalGiven P₁ m₁ u₁ q₁) (h₂ : IsOptimalGiven P₂ m₂ u₂ q₂) : u₂ ≤ u₁ := by
  have hn0' : 0 < P₂.nbar := hn ▸ hn0
  have hθ0' : 0 < P₂.θ := hθ ▸ hθ0
  rw [optGiven_iff P₁ hk₁ hk₁' hθ0 hn0 m₁ hm₁] at h₁
  rw [optGiven_iff P₂ hk₂ hk₂' hθ0' hn0' m₂ hm₂] at h₂
  have hmem₂ := qh_mem P₂ hk₂ hk₂' hn0' m₂ hm₂
  have hge := ff_ge P₁ hk₁ hk₁' hn0 m₁ hm₁ (qh P₂ m₂) hmem₂.1
  have hsq : 0 ≤ P₁.k' / (2 * P₁.nbar) * (qh P₂ m₂ - qh P₁ m₁) ^ 2 := by positivity
  have hle : ffs P₁ m₁ ≤ ffs P₂ m₂ := by
    have := hff (qh P₂ m₂) hmem₂.1
    have e : ffs P₂ m₂ = ff P₂ m₂ (qh P₂ m₂) := rfl
    have e1 : ffs P₁ m₁ = ff P₁ m₁ (qh P₁ m₁) := rfl
    linarith
  have hs₁ := ffs_pos P₁ hk₁ hk₁' hn0 m₁ hm₁
  rw [h₁.1, h₂.1, hθ, hn]
  apply div_le_div_of_nonneg_left (by rw [← hθ, ← hn]; positivity) (by positivity)
  linarith

theorem solution (P : Params)
    (hk : 0 < P.k) (hkk' : P.k < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar) :
    (∀ m₁ m₂ u₁ q₁ u₂ q₂ : ℝ, 1 ≤ m₁ → m₁ ≤ m₂ →
        IsOptimalGiven P m₁ u₁ q₁ → IsOptimalGiven P m₂ u₂ q₂ → u₂ ≤ u₁) ∧
    (∀ k₂' : ℝ, P.k' < k₂' → ∀ m u₁ q₁ u₂ q₂ : ℝ, 1 ≤ m →
        IsOptimalGiven P m u₁ q₁ → IsOptimalGiven { P with k' := k₂' } m u₂ q₂ → u₂ ≤ u₁) := by
  have hk' : 0 < P.k' := by linarith
  constructor
  · intro m₁ m₂ u₁ q₁ u₂ q₂ h1 h12 hA hB
    refine mono_u P P rfl rfl hk hk' hk hk' hθ hn m₁ m₂ (by linarith) (by linarith) ?_ u₁ q₁ u₂ q₂ hA hB
    intro q hq
    unfold ff
    nlinarith [mul_nonneg (mul_nonneg hk.le hq) (sub_nonneg.mpr h12)]
  · intro k₂' hlt m u₁ q₁ u₂ q₂ hm hA hB
    have hk2 : 0 < k₂' := by linarith
    refine mono_u P { P with k' := k₂' } rfl rfl hk hk' hk hk2 hθ hn m m (by linarith) (by linarith) ?_ u₁ q₁ u₂ q₂ hA hB
    intro q hq
    unfold ff
    dsimp only
    nlinarith [mul_nonneg (sub_nonneg.mpr hlt.le) (div_nonneg (sq_nonneg (P.nbar - q)) (by positivity : (0:ℝ) ≤ 2 * P.nbar))]
