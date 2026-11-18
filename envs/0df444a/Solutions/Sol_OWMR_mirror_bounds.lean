-- Prove2me | solution 1 for OWMR.mirror_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:06.629208+00:00
-- url     : https://prove2.me/submissions/e16e6a8e-c83f-46ae-b00a-400760d46792

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewal_depletion_mean
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Lemma 4, mirror bounds `B_w ≤ β w` and `B_w ≤ h 𝔼 X_w ≤ h w / 2`, for the width-`w` policy
`(s, S)` with `w = S - s`. Each bound evaluates the mirror loss at one fixed center: `z = hw/(h+p)`
for the first and `z = 0` for the second, through the occupation identity (10) and, for the
second, the mean-depletion bound of Lemma 2.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

private lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

private lemma intOn (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {a e : ℝ} (ha : 0 ≤ a) :
    IntegrableOn φ (Set.Ico a e) (renewalMeasure ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C)
    (ne_top_of_le_ne_top (renewalMeasure_Ico_lt_top ρ hρ e).ne
      (measure_mono (Set.Ico_subset_Ico_left ha))) hφ.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hC x (Set.Ico_subset_Icc_self hx)

private lemma bdd_of_cont {φ : ℝ → ℝ} (hφ : Continuous φ) (c e : ℝ) :
    ∃ C, ∀ y ∈ Set.Icc c e, φ y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

private lemma mirrorAvg_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    mirrorAvg ρ h p s S a = ssAvgCost ρ (fun y => whLoss h p (a - y)) 0 s S := by
  unfold mirrorAvg ssAvgCost ssPeriodCost
  simp only [zero_mul, zero_add]

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p s S : ℝ) (hh : 0 < h) (hp : 0 < p) (hsS : s < S) :
    mirrorCost ρ h p s S ≤ ENNReal.ofReal (h * p / (h + p) * (S - s)) ∧
      mirrorCost ρ h p s S ≤ ENNReal.ofReal (h * (S - s) / 2) := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = S - s := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : 0 < w := by rw [hw]; linarith
  have hUw : renewalMeasure ρ (Set.Ico 0 w) ≠ ∞ := (renewalMeasure_Ico_lt_top ρ hρ w).ne
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (renewalMeasure ρ (Set.Ico 0 w)).toReal := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_mono hUw (one_le_renewal ρ w hw0)
    simpa [hM] using this
  have hM0 : 0 < M := by linarith
  have hφc : ∀ a : ℝ, Continuous fun y => whLoss h p (a - y) := fun a => by
    unfold whLoss; fun_prop
  have hφ0 : ∀ a y : ℝ, 0 ≤ whLoss h p (a - y) := fun a y =>
    add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))
  -- the occupation identity (10) for the mirror loss at center `a`
  have hmir : ∀ a : ℝ, mirrorAvg ρ h p s S a = ENNReal.ofReal
      ((∫ x in Set.Ico 0 w, whLoss h p (a - (S - x)) ∂renewalMeasure ρ) / M) := by
    intro a
    rw [mirrorAvg_eq, ss_renewal_reward ρ hρ _ (hφc a).measurable (hφ0 a) 0 s S le_rfl hsS
      (bdd_of_cont (hφc a) s S), zero_add, ← hw, ← hM]
  have hcont : ∀ a : ℝ, Continuous fun x => whLoss h p (a - (S - x)) := fun a =>
    (hφc a).comp (continuous_const.sub continuous_id)
  constructor
  · -- center `z = hw/(h+p)`: the loss is at most `β w` on `[0, w]`
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = h * w / (h + p) := ⟨_, rfl⟩
    have key1 : h * (w - z) = h * p / (h + p) * w := by
      rw [hz]; field_simp; try ring
    have key2 : p * z = h * p / (h + p) * w := by
      rw [hz]; field_simp; try ring
    have hpt : ∀ x ∈ Set.Ico 0 w, whLoss h p ((S - z) - (S - x)) ≤ h * p / (h + p) * w := by
      intro x hx
      unfold whLoss
      rw [show S - z - (S - x) = x - z by ring]
      rcases le_total z x with hzx | hxz
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        have := mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2.le z) hh.le
        linarith
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        have := mul_le_mul_of_nonneg_left (by linarith [hx.1] : z - x ≤ z) hp.le
        linarith
    have hint : ∫ x in Set.Ico 0 w, whLoss h p ((S - z) - (S - x)) ∂renewalMeasure ρ
        ≤ h * p / (h + p) * w * M := by
      calc ∫ x in Set.Ico 0 w, whLoss h p ((S - z) - (S - x)) ∂renewalMeasure ρ
          ≤ ∫ _x in Set.Ico 0 w, h * p / (h + p) * w ∂renewalMeasure ρ :=
            setIntegral_mono_on (intOn ρ hρ (hcont (S - z)) le_rfl) (integrableOn_const hUw)
              measurableSet_Ico hpt
        _ = h * p / (h + p) * w * M := by
            rw [setIntegral_const, smul_eq_mul, measureReal_def, ← hM, mul_comm]
    calc mirrorCost ρ h p s S ≤ mirrorAvg ρ h p s S (S - z) :=
          iInf_le (fun a => mirrorAvg ρ h p s S a) (S - z)
      _ = ENNReal.ofReal ((∫ x in Set.Ico 0 w, whLoss h p ((S - z) - (S - x))
            ∂renewalMeasure ρ) / M) := hmir (S - z)
      _ ≤ ENNReal.ofReal (h * p / (h + p) * w) :=
          ENNReal.ofReal_le_ofReal ((div_le_iff₀ hM0).2 hint)
  · -- center `z = 0`: the loss is `h x`, and Lemma 2 bounds the mean depletion
    have hpt : ∀ x ∈ Set.Ico 0 w, whLoss h p (S - (S - x)) = h * x := by
      intro x hx
      unfold whLoss
      rw [show S - (S - x) = x by ring, max_eq_left hx.1, max_eq_right (by linarith [hx.1])]
      ring
    have hmean : ∫ x in Set.Ico 0 w, x ∂renewalMeasure ρ ≤ w / 2 * M := by
      have hnn : 0 ≤ᵐ[(renewalMeasure ρ).restrict (Set.Ico 0 w)] fun x : ℝ => x :=
        ae_restrict_of_forall_mem measurableSet_Ico fun x hx => hx.1
      rw [integral_eq_lintegral_of_nonneg_ae hnn continuous_id.aestronglyMeasurable]
      have hE := renewal_depletion_mean ρ w hw0.le
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUw) hE
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ← hM] at this
    have hint : ∫ x in Set.Ico 0 w, whLoss h p (S - (S - x)) ∂renewalMeasure ρ ≤ h * w / 2 * M := by
      rw [setIntegral_congr_fun measurableSet_Ico hpt, integral_const_mul]
      have := mul_le_mul_of_nonneg_left hmean hh.le
      linarith
    calc mirrorCost ρ h p s S ≤ mirrorAvg ρ h p s S S :=
          iInf_le (fun a => mirrorAvg ρ h p s S a) S
      _ = ENNReal.ofReal ((∫ x in Set.Ico 0 w, whLoss h p (S - (S - x))
            ∂renewalMeasure ρ) / M) := hmir S
      _ ≤ ENNReal.ofReal (h * w / 2) :=
          ENNReal.ofReal_le_ofReal ((div_le_iff₀ hM0).2 hint)
