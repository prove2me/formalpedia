-- Prove2me | solution 1 for PersPricingDist.PersonalA.pp_beta_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:31:47.809873+00:00
-- url     : https://prove2.me/submissions/8c8817dd-63a8-486b-a1a7-5da9e0082cf2

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting
import Theorems.Thm_PersPricingDist_PersonalA_pp_cutoff
import Theorems.Thm_PersPricingDist_PersonalA_contributions

open PersPricingDist.PersonalA

namespace PPDAProp4Aux

/-- A continuous strictly increasing function on `[c,1]`, negative at `c` and positive at `1`,
has a unique root `t0 ∈ (c,1)`, and it is positive exactly to the right of `t0`. -/
lemma root_threshold {c : ℝ} (hc : c < 1) (f : ℝ → ℝ) (hcont : ContinuousOn f (Set.Icc c 1))
    (hmono : StrictMonoOn f (Set.Icc c 1)) (h0 : f c < 0) (h1 : 0 < f 1) :
    ∃ t0 ∈ Set.Ioo c 1, f t0 = 0 ∧ ∀ t ∈ Set.Icc c 1, (0 < f t ↔ t0 < t) := by
  obtain ⟨t0, ht0, hf⟩ := intermediate_value_Icc hc.le hcont
    (show (0:ℝ) ∈ Set.Icc (f c) (f 1) from ⟨h0.le, h1.le⟩)
  have hne1 : t0 ≠ c := by rintro rfl; linarith
  have hne2 : t0 ≠ 1 := by rintro rfl; linarith
  refine ⟨t0, ⟨lt_of_le_of_ne ht0.1 (Ne.symm hne1), lt_of_le_of_ne ht0.2 hne2⟩, hf, ?_⟩
  intro t ht
  rw [← hf]
  exact hmono.lt_iff_lt ht0 ht

/-- PP sign polynomial in the parametrization `v = 1 - c t`, `s = 1 - t^2`. -/
def hPP (c t : ℝ) : ℝ := (1 + c) * t ^ 2 + t - (1 + 2 * c)

/-- The factor `(2+5s+s^2)/(1+2s)` in the PU cutoff. -/
noncomputable def E (s : ℝ) : ℝ := (2 + 5 * s + s ^ 2) / (1 + 2 * s)

/-- PU sign function in the parametrization `v = 1 - c t`, `s = 1 - t^2`. -/
noncomputable def kPU (c t : ℝ) : ℝ :=
  t - 2 * c + c * t ^ 2 - (1 - t ^ 2) * Real.sqrt (E (1 - t ^ 2))

/-- `β` in the parametrization. -/
noncomputable def g (c t : ℝ) : ℝ := (t - c) ^ 2 / (2 * (1 - t ^ 2))

lemma E_eq {s : ℝ} (hs : 0 ≤ s) : E s = s / 2 + 9 / 4 - 1 / (4 * (1 + 2 * s)) := by
  unfold E
  have : (1 + 2 * s) ≠ 0 := by linarith
  field_simp
  ring

lemma E_pos {s : ℝ} (hs : 0 ≤ s) : 0 < E s := by
  unfold E
  apply div_pos <;> nlinarith

lemma E_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : E a ≤ E b := by
  rw [E_eq ha, E_eq (ha.trans hab)]
  have h1 : 1 / (4 * (1 + 2 * b)) ≤ 1 / (4 * (1 + 2 * a)) := by
    apply one_div_le_one_div_of_le <;> nlinarith
  linarith

lemma hPP_mono {c : ℝ} (hc : 0 ≤ c) : StrictMonoOn (hPP c) (Set.Icc c 1) := by
  intro a ha b hb hab
  unfold hPP
  have ha0 : 0 ≤ a := hc.trans ha.1
  nlinarith [mul_pos (by linarith : (0:ℝ) < b - a) (by linarith : (0:ℝ) < b + a + 1),
    mul_nonneg hc (mul_nonneg (by linarith : (0:ℝ) ≤ b - a) (by linarith : (0:ℝ) ≤ b + a))]

lemma kPU_mono {c : ℝ} (hc : 0 ≤ c) : StrictMonoOn (kPU c) (Set.Icc c 1) := by
  intro a ha b hb hab
  unfold kPU
  have ha0 : 0 ≤ a := hc.trans ha.1
  have hsb : 0 ≤ 1 - b ^ 2 := by nlinarith [hb.2]
  have hsab : 1 - b ^ 2 ≤ 1 - a ^ 2 := by nlinarith
  have hE : Real.sqrt (E (1 - b ^ 2)) ≤ Real.sqrt (E (1 - a ^ 2)) :=
    Real.sqrt_le_sqrt (E_mono hsb hsab)
  have key : (1 - b ^ 2) * Real.sqrt (E (1 - b ^ 2)) ≤ (1 - a ^ 2) * Real.sqrt (E (1 - a ^ 2)) :=
    mul_le_mul hsab hE (Real.sqrt_nonneg _) (hsb.trans hsab)
  have h2 : c * a ^ 2 ≤ c * b ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc
  linarith

lemma hPP_cont (c : ℝ) : ContinuousOn (hPP c) (Set.Icc c 1) := by
  unfold hPP
  fun_prop

lemma kPU_cont {c : ℝ} (hc : 0 ≤ c) : ContinuousOn (kPU c) (Set.Icc c 1) := by
  unfold kPU E
  apply ContinuousOn.sub (by fun_prop)
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.sqrt
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2, hc.trans ht.1]
  nlinarith

lemma g_mono {c : ℝ} (hc : 0 ≤ c) : StrictMonoOn (g c) (Set.Ioo c 1) := by
  intro a ha b hb hab
  unfold g
  have hb1 : 0 < 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
  have ha1 : 1 - b ^ 2 < 1 - a ^ 2 := by nlinarith [ha.1]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have hsq : (a - c) ^ 2 < (b - c) ^ 2 := by nlinarith [ha.1]
  have e1 : (a - c) ^ 2 * (2 * (1 - b ^ 2)) ≤ (a - c) ^ 2 * (2 * (1 - a ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have e2 : (a - c) ^ 2 * (2 * (1 - a ^ 2)) < (b - c) ^ 2 * (2 * (1 - a ^ 2)) :=
    mul_lt_mul_of_pos_right hsq (by linarith)
  linarith

/-- Sign identity for the PP cutoff. -/
lemma pp_identity (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht2 : t ^ 2 < 1) :
    (1 - c * t - Model.vTilde (1 - t ^ 2)) * (1 + (1 - t ^ 2)) = t * hPP c t := by
  unfold Model.vTilde hPP
  rw [show 1 - (1 - t ^ 2) = t ^ 2 by ring, Real.sqrt_sq ht]
  have : (1 + (1 - t ^ 2)) ≠ 0 := by nlinarith
  field_simp
  ring

/-- Sign identity for the PU cutoff. -/
lemma pu_identity (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht2 : t ^ 2 < 1) :
    (1 - c * t - Model.vCheck (1 - t ^ 2)) * (1 + (1 - t ^ 2)) = t * kPU c t := by
  unfold Model.vCheck kPU
  have hsq : Real.sqrt ((1 - (1 - t ^ 2)) * (2 + 5 * (1 - t ^ 2) + (1 - t ^ 2) ^ 2)
      / (1 + 2 * (1 - t ^ 2))) = t * Real.sqrt (E (1 - t ^ 2)) := by
    rw [show 1 - (1 - t ^ 2) = t ^ 2 by ring, mul_div_assoc, Real.sqrt_mul (sq_nonneg t),
      Real.sqrt_sq ht]
    rfl
  rw [hsq]
  have : (1 + (1 - t ^ 2)) ≠ 0 := by nlinarith
  field_simp
  ring

lemma pp_iff (c : ℝ) {t : ℝ} (ht : 0 < t) (ht2 : t ^ 2 < 1) :
    Model.vTilde (1 - t ^ 2) < 1 - c * t ↔ 0 < hPP c t := by
  have hid := pp_identity c ht.le ht2
  have hp : 0 < 1 + (1 - t ^ 2) := by nlinarith
  constructor
  · intro h
    have : 0 < t * hPP c t := by rw [← hid]; exact mul_pos (by linarith) hp
    exact pos_of_mul_pos_right this ht.le
  · intro h
    have : 0 < (1 - c * t - Model.vTilde (1 - t ^ 2)) * (1 + (1 - t ^ 2)) := by
      rw [hid]; exact mul_pos ht h
    have := pos_of_mul_pos_left this hp.le
    linarith

lemma pu_iff (c : ℝ) {t : ℝ} (ht : 0 < t) (ht2 : t ^ 2 < 1) :
    Model.vCheck (1 - t ^ 2) < 1 - c * t ↔ 0 < kPU c t := by
  have hid := pu_identity c ht.le ht2
  have hp : 0 < 1 + (1 - t ^ 2) := by nlinarith
  constructor
  · intro h
    have : 0 < t * kPU c t := by rw [← hid]; exact mul_pos (by linarith) hp
    exact pos_of_mul_pos_right this ht.le
  · intro h
    have : 0 < (1 - c * t - Model.vCheck (1 - t ^ 2)) * (1 + (1 - t ^ 2)) := by
      rw [hid]; exact mul_pos ht h
    have := pos_of_mul_pos_left this hp.le
    linarith

lemma pp_exists (c : ℝ) (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    ∃ t0 ∈ Set.Ioo c 1, hPP c t0 = 0 ∧ ∀ t ∈ Set.Icc c 1, (0 < hPP c t ↔ t0 < t) := by
  apply root_threshold hc.2 _ (hPP_cont c) (hPP_mono hc.1.le)
  · unfold hPP; nlinarith [hc.1, hc.2, mul_pos hc.1 hc.1]
  · unfold hPP; nlinarith [hc.2]

lemma pu_exists (c : ℝ) (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    ∃ t0 ∈ Set.Ioo c 1, kPU c t0 = 0 ∧ ∀ t ∈ Set.Icc c 1, (0 < kPU c t ↔ t0 < t) := by
  apply root_threshold hc.2 _ (kPU_cont hc.1.le) (kPU_mono hc.1.le)
  · unfold kPU
    have h1 : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
    have h2 : 0 < Real.sqrt (E (1 - c ^ 2)) := Real.sqrt_pos.mpr (E_pos h1.le)
    nlinarith [mul_pos h1 h2, mul_pos hc.1 h1]
  · unfold kPU; simp; linarith [hc.2]

/-- Parametrization of an admissible market by `c = √(2α)` and `t = √(1-s)`. -/
lemma param (M : Model) (hM : M.Standing) :
    Real.sqrt (2 * M.alpha) ∈ Set.Ioo (0:ℝ) 1 ∧
    Real.sqrt (1 - M.s) ∈ Set.Ioo (Real.sqrt (2 * M.alpha)) 1 ∧
    M.v = 1 - Real.sqrt (2 * M.alpha) * Real.sqrt (1 - M.s) ∧
    M.s = 1 - Real.sqrt (1 - M.s) ^ 2 ∧
    M.beta = g (Real.sqrt (2 * M.alpha)) (Real.sqrt (1 - M.s)) := by
  obtain ⟨hα, hβ⟩ := contributions M hM
  have hs0 := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  set c := Real.sqrt (2 * M.alpha) with hc
  set t := Real.sqrt (1 - M.s) with ht
  have h1s : 0 < 1 - M.s := by linarith
  have ht2 : t ^ 2 = 1 - M.s := Real.sq_sqrt h1s.le
  have htpos : 0 < t := Real.sqrt_pos.mpr h1s
  have hαpos : 0 < M.alpha := by rw [hα]; apply div_pos <;> nlinarith
  have hc2 : c ^ 2 = 2 * M.alpha := Real.sq_sqrt (by linarith)
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hct : c * t = 1 - M.v := by
    have hsq : (c * t) ^ 2 = (1 - M.v) ^ 2 := by
      rw [mul_pow, hc2, ht2, hα]
      field_simp
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by linarith)] at h
  have ht1 : t < 1 := by nlinarith
  have hct' : c < t := by
    by_contra hcon
    push Not at hcon
    have : t * t ≤ c * t := mul_le_mul_of_nonneg_right hcon htpos.le
    nlinarith
  refine ⟨⟨hcpos, by linarith⟩, ⟨hct', ht1⟩, by linarith, by linarith, ?_⟩
  rw [hβ]
  unfold g
  have hvs : M.v - M.s = t * (t - c) := by nlinarith
  have hs' : M.s = 1 - t ^ 2 := by linarith
  rw [hvs, hs']
  have h1 : (1 - t ^ 2) ≠ 0 := by nlinarith
  have h2 : 1 - (1 - t ^ 2) = t ^ 2 := by ring
  rw [h2]
  field_simp

end PPDAProp4Aux

open PPDAProp4Aux in
theorem solution :
    ∃ betaPP : ℝ → ℝ,
      ∀ M : Model, M.Standing → (M.DualPP ↔ betaPP M.alpha < M.beta) := by
  choose T1 hT1 using pp_exists
  refine ⟨fun a => if h : Real.sqrt (2 * a) ∈ Set.Ioo (0:ℝ) 1 then
              g (Real.sqrt (2 * a)) (T1 (Real.sqrt (2 * a)) h) else 0, ?_⟩
  intro M hM
  obtain ⟨hc, ht, hv, hs, hb⟩ := param M hM
  simp only [dif_pos hc]
  rw [pp_cutoff M hM, hb]
  obtain ⟨hT, _, hiff⟩ := hT1 _ hc
  have htp : 0 < Real.sqrt (1 - M.s) := hc.1.trans ht.1
  have ht2 : Real.sqrt (1 - M.s) ^ 2 < 1 := by nlinarith [ht.2]
  have key : Model.vTilde M.s < M.v ↔ Model.vTilde (1 - Real.sqrt (1 - M.s) ^ 2) <
      1 - Real.sqrt (2 * M.alpha) * Real.sqrt (1 - M.s) := by rw [← hs, ← hv]
  rw [key, pp_iff _ htp ht2, hiff _ ⟨ht.1.le, ht.2.le⟩, (g_mono hc.1.le).lt_iff_lt hT ht]
