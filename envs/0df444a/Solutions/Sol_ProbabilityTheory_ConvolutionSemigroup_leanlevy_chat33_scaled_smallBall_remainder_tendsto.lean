-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_smallBall_remainder_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:36:26.922198+00:00
-- url     : https://prove2.me/submissions/42059a01-fc3f-46a7-8db4-6a03066dd85b

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_exists_atomFree_seq_tendsto_zero
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_remainder_band_tendsto
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_ball_split
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball_levy
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_inner_ball_norm_le
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball_levy
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Positivity
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real
/-- Original-source small-ball remainder, using the proved band and inner-ball bounds. -/
theorem solution (S : ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C)
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) * ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  rcases eq_or_ne ξ 0 with hξ0 | hξ0
  · subst hξ0
    have hint0 : ∀ (m : Measure ℝ),
        ∫ x in {x : ℝ | |x| < r},
          (exp ((↑x : ℂ) * ↑(0:ℝ) * I) - 1 - (↑x : ℂ) * ↑(0:ℝ) * I
            + ((↑x : ℂ) * ↑(0:ℝ)) ^ 2 / 2) ∂m = 0 := by
      intro m
      have : (fun x : ℝ => exp ((↑x : ℂ) * ↑(0:ℝ) * I) - 1 - (↑x : ℂ) * ↑(0:ℝ) * I
            + ((↑x : ℂ) * ↑(0:ℝ)) ^ 2 / 2) = fun _ : ℝ => (0 : ℂ) := by
        funext x; simp
      simp only [this, integral_zero]
    simp only [hint0, mul_zero]
    exact tendsto_const_nhds
  obtain ⟨C, hC⟩ := hσ_bdd
  have hξ_pos : 0 < |ξ| := abs_pos.mpr hξ0
  have hc_pos : 0 < min r (1 / |ξ|) := lt_min hr (by positivity)
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_atom, hδ_lim⟩ := hν.exists_atomFree_seq_tendsto_zero hc_pos
  have hδ_ltr : ∀ m, δ m < r := fun m => (hδ_lt m).trans_le (min_le_left _ _)
  have hδ_le1 : ∀ m, δ m ≤ 1 := fun m => le_of_lt ((hδ_ltr m).trans_le hr1)
  have hδξ : ∀ m, δ m * |ξ| ≤ 1 := fun m => by
    have h := (hδ_lt m).trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hξ_pos] at h
    exact le_of_lt h
  set Bν : ℝ := ∫ x in {x | |x| < r}, x ^ 2 ∂ν with hBν_def
  have hν_inner_sq_le : ∀ m, ∫ x in {x | |x| < δ m}, x ^ 2 ∂ν ≤ Bν := by
    intro m
    refine setIntegral_mono_set (leanlevy_chat32_sq_integrableOn_ball_levy hν r)
      (ae_restrict_of_forall_mem
        ((isOpen_lt continuous_abs continuous_const).measurableSet) (fun x _ => sq_nonneg x))
      (LE.le.eventuallyLE (fun x hx => lt_trans hx (hδ_ltr m)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htendC : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C) atTop (𝓝 0) := by
    have : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C) atTop
        (𝓝 ((2 / 9 : ℝ) * |ξ| ^ 3 * 0 * C)) := by
      exact ((tendsto_const_nhds.mul hδ_lim).mul tendsto_const_nhds)
    simpa using this
  have htendBν : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν) atTop (𝓝 0) := by
    have : Tendsto (fun m => (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν) atTop
        (𝓝 ((2 / 9 : ℝ) * |ξ| ^ 3 * 0 * Bν)) := by
      exact ((tendsto_const_nhds.mul hδ_lim).mul tendsto_const_nhds)
    simpa using this
  have hevC : ∀ᶠ m in atTop, (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C < ε / 3 :=
    htendC.eventually_lt_const (by linarith)
  have hevBν : ∀ᶠ m in atTop, (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν < ε / 3 :=
    htendBν.eventually_lt_const (by linarith)
  obtain ⟨m, hmC, hmBν⟩ := (hevC.and hevBν).exists
  have h_band_lim := ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_remainder_band_tendsto S (hδ_pos m) (hδ_ltr m) hr1 ξ hν (hδ_atom m) hν_r h_jump
  rw [Metric.tendsto_atTop] at h_band_lim
  obtain ⟨N, hN⟩ := h_band_lim (ε / 3) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  set μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ) with hμk_def
  set tk : ℝ := (t_seq k).val⁻¹ with htk_def
  set ck : ℂ := ((t_seq k).val⁻¹ : ℂ) with hck_def
  have htk_pos : 0 < tk := inv_pos.mpr (t_seq k).2
  have hck_eq : ck = (↑tk : ℂ) := by rw [hck_def, htk_def]; push_cast; ring
  have hsplit_μ := leanlevy_chat32_remainder_ball_split (hδ_pos m) (hδ_ltr m) hr1 ξ μk (leanlevy_chat32_remainder_integrableOn_ball (le_of_lt hr) hr1 ξ μk)
  have hsplit_ν := leanlevy_chat32_remainder_ball_split (hδ_pos m) (hδ_ltr m) hr1 ξ ν
    (leanlevy_chat32_remainder_integrableOn_ball_levy hr1 ξ hν)
  set iμ : ℂ := ∫ x in {x | |x| < δ m},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk with hiμ_def
  set bμ : ℂ := ∫ x in {x | δ m ≤ |x| ∧ |x| < r},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk with hbμ_def
  set iν : ℂ := ∫ x in {x | |x| < δ m},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν with hiν_def
  set bν : ℂ := ∫ x in {x | δ m ≤ |x| ∧ |x| < r},
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν with hbν_def
  rw [dist_eq_norm]
  rw [hsplit_μ, hsplit_ν]
  rw [show ck * (iμ + bμ) - (iν + bν) = (ck * iμ - iν) + (ck * bμ - bν) from by ring]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  have hband_lt : ‖ck * bμ - bν‖ < ε / 3 := by
    rw [hbμ_def, hbν_def, hck_def, hμk_def]
    have hth := hN k hk
    rwa [dist_eq_norm] at hth
  have hinner_lt : ‖ck * iμ - iν‖ < ε / 3 + ε / 3 := by
    refine lt_of_le_of_lt (norm_sub_le _ _) ?_
    have hμ_norm : ‖ck * iμ‖ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C := by
      rw [hck_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htk_pos, hiμ_def]
      calc tk * ‖∫ x in {x | |x| < δ m},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂μk‖
          ≤ tk * ((2 / 9 : ℝ) * |ξ| ^ 3 * δ m * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt htk_pos)
            exact leanlevy_chat32_remainder_inner_ball_norm_le (hδ_pos m) (hδ_le1 m) ξ (hδξ m) μk
              (leanlevy_chat32_remainder_integrableOn_ball (le_of_lt (hδ_pos m)) (hδ_le1 m) ξ μk)
              (leanlevy_chat32_sq_integrableOn_ball (δ m) μk)
        _ = (2 / 9 : ℝ) * |ξ| ^ 3 * δ m *
              (tk * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk) := by ring
        _ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C := by
            refine mul_le_mul_of_nonneg_left ?_ (by have := hδ_pos m; positivity)
            calc tk * ∫ x in {x | |x| < δ m}, x ^ 2 ∂μk
                ≤ tk * ∫ x in {x | |x| < r}, x ^ 2 ∂μk := by
                  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt htk_pos)
                  refine setIntegral_mono_set (leanlevy_chat32_sq_integrableOn_ball r μk)
                    (ae_restrict_of_forall_mem
                      ((isOpen_lt continuous_abs continuous_const).measurableSet)
                      (fun x _ => sq_nonneg x))
                    (LE.le.eventuallyLE (fun x hx => lt_trans hx (hδ_ltr m)))
              _ ≤ C := hC k
    have hν_norm : ‖iν‖ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν := by
      rw [hiν_def]
      calc ‖∫ x in {x | |x| < δ m},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν‖
          ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * ∫ x in {x | |x| < δ m}, x ^ 2 ∂ν :=
            leanlevy_chat32_remainder_inner_ball_norm_le (hδ_pos m) (hδ_le1 m) ξ (hδξ m) ν
              (leanlevy_chat32_remainder_integrableOn_ball_levy (hδ_le1 m) ξ hν)
              (leanlevy_chat32_sq_integrableOn_ball_levy hν (δ m))
        _ ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν := by
            refine mul_le_mul_of_nonneg_left (hν_inner_sq_le m) (by have := hδ_pos m; positivity)
    calc ‖ck * iμ‖ + ‖iν‖
        ≤ (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * C + (2 / 9 : ℝ) * |ξ| ^ 3 * δ m * Bν :=
          add_le_add hμ_norm hν_norm
      _ < ε / 3 + ε / 3 := by linarith [hmC, hmBν]
  linarith [hband_lt, hinner_lt]
