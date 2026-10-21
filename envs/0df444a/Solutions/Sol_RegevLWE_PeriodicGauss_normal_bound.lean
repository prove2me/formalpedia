-- Prove2me | solution 1 for RegevLWE.PeriodicGauss.normal_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:58:06.196142+00:00
-- url     : https://prove2.me/submissions/901b0c35-fea2-414d-84fe-2bf1b3e51582

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

set_option autoImplicit false
open MeasureTheory RegevLWE.PeriodicGauss


theorem RLP_first_display (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - 1 / (1 + ϵ) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ≤
      (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) +
      (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) = ENNReal.ofReal ϵ ∧
    (∫⁻ x : ℝ, ENNReal.ofReal
        |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) =
      ∫⁻ x : ℝ, ENNReal.ofReal
        (|Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1| *
          Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) := by
  have hs : 0 < 1 + ϵ := by linarith
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ ∫⁻ x : ℝ, (ENNReal.ofReal
          |Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)| +
          ENNReal.ofReal
          |(1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)|) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : Real.exp (-Real.pi * x ^ 2) - 1 / (1 + ϵ) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)
              = (Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) +
                (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by ring
          rw [this]
          exact abs_add_le _ _
      _ = _ := by
          refine lintegral_add_left ?_ _
          fun_prop
  · have hnn : ∀ x : ℝ, 0 ≤ (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      intro x
      have : 0 ≤ 1 - 1 / (1 + ϵ) := by
        rw [sub_nonneg, div_le_one hs]; linarith
      positivity
    have hb : 0 < Real.pi / (1 + ϵ) ^ 2 := by positivity
    have hexp : ∀ x : ℝ, Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        Real.exp (-(Real.pi / (1 + ϵ) ^ 2) * x ^ 2) := fun x => by congr 1; ring
    have hint : Integrable (fun x : ℝ => (1 - 1 / (1 + ϵ)) *
        Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2)) := by
      simp_rw [hexp]
      exact (integrable_exp_neg_mul_sq hb).const_mul _
    have hI : ∫ x : ℝ, (1 - 1 / (1 + ϵ)) * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) = ϵ := by
      simp_rw [hexp]
      rw [integral_const_mul, integral_gaussian]
      have : Real.pi / (Real.pi / (1 + ϵ) ^ 2) = (1 + ϵ) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hs.le]
      field_simp
      ring
    have := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)
    rw [hI] at this
    rw [this]
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (hnn x)]
  · refine lintegral_congr fun x => ?_
    congr 1
    have e : Real.exp (-Real.pi * x ^ 2) = Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) *
        Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-Real.pi * x ^ 2) - Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        (Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1) *
          Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) := by
      rw [e]; ring
    rw [h2, abs_mul, abs_of_pos (Real.exp_pos _)]


lemma RLP_gauss2 (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = b ^ (-(3 : ℝ) / 2) * (Real.sqrt Real.pi / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := b) two_pos (by norm_num) hb
  simp_rw [Real.rpow_two] at h
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
    have : ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have e : ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) =
      ∫ x : ℝ, (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) |x| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  have hca := integral_comp_abs (f := fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2))
  rw [e, hca, h, hG]
  have : -((2 : ℝ) + 1) / 2 = -(3 : ℝ) / 2 := by norm_num
  rw [this]
  ring

theorem RLP_final_evaluation (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    ϵ + 2 * Real.pi * ϵ * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        ϵ + ϵ * (1 + ϵ) ^ 3 ∧
      ϵ + ϵ * (1 + ϵ) ^ 3 ≤ 9 * ϵ := by
  refine ⟨?_, by nlinarith [mul_pos hϵ hϵ, mul_pos (mul_pos hϵ hϵ) hϵ]⟩
  have hs : 0 < 1 + ϵ := by linarith
  have hpi := Real.pi_pos
  set s := 1 + ϵ with hsdef
  have hb : 0 < Real.pi / s ^ 2 := by positivity
  have hint : ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / s ^ 2) =
      ∫ x : ℝ, x ^ 2 * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    congr 2
    ring
  rw [hint, RLP_gauss2 _ hb]
  -- b^(-3/2) = s^3 / π^(3/2)
  have hc : (Real.pi / s ^ 2) ^ (-(3 : ℝ) / 2) = s ^ 3 / (Real.sqrt Real.pi) ^ 3 := by
    have h1 : Real.pi / s ^ 2 = (Real.sqrt Real.pi / s) ^ (2 : ℕ) := by
      rw [div_pow, Real.sq_sqrt hpi.le]
    have hc0 : 0 < Real.sqrt Real.pi / s := by positivity
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    have : ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg hc0.le, Real.rpow_natCast, div_pow, inv_div]
  rw [hc]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have h3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, hsq]
  have h4 : s ^ 3 / Real.sqrt Real.pi ^ 3 * (Real.sqrt Real.pi / 2) = s ^ 3 / (2 * Real.pi) := by
    rw [h3]; field_simp
  rw [h4]
  field_simp

lemma RLP_scale (F : ℝ → ENNReal) (α : ℝ) (hα : 0 < α) :
    ∫⁻ x, F x = ∫⁻ y, ENNReal.ofReal α * F (α * y) := by
  have h1 : ∫⁻ y, F (α * y) = ENNReal.ofReal |α⁻¹| * ∫⁻ x, F x := by
    have hemb := (Homeomorph.mulLeft₀ α hα.ne').measurableEmbedding
    have := hemb.lintegral_map (μ := volume) F
    have hmap : Measure.map (Homeomorph.mulLeft₀ α hα.ne') volume =
        ENNReal.ofReal |α⁻¹| • volume := Real.map_volume_mul_left hα.ne'
    rw [hmap, lintegral_smul_measure] at this
    simpa using this.symm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, ← mul_assoc,
    ← ENNReal.ofReal_mul hα.le, abs_of_pos (inv_pos.2 hα), mul_inv_cancel₀ hα.ne']
  simp

lemma RLP_nu_scaled (α ε y : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    α * ((1 / α) * Real.exp (-Real.pi * (α * y / α) ^ 2) -
      (1 / (α * (1 + ε))) * Real.exp (-Real.pi * (α * y / (α * (1 + ε))) ^ 2)) =
    Real.exp (-Real.pi * y ^ 2) - 1 / (1 + ε) * Real.exp (-Real.pi * y ^ 2 / (1 + ε) ^ 2) := by
  have hs : 0 < 1 + ε := by linarith
  have e1 : α * y / α = y := by field_simp
  have e2 : α * y / (α * (1 + ε)) = y / (1 + ε) := by field_simp
  rw [e1, e2, div_pow]
  have e3 : -Real.pi * (y ^ 2 / (1 + ε) ^ 2) = -Real.pi * y ^ 2 / (1 + ε) ^ 2 := by ring
  rw [e3]
  field_simp

theorem solution (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β ≤ 2 * α) :
    statDist (nu α) (nu β) ≤ ENNReal.ofReal (9 * (β / α - 1)) := by
  set ε : ℝ := β / α - 1 with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, one_lt_div hα]; exact hαβ
  have hε1 : ε ≤ 1 := by
    rw [hε, sub_le_iff_le_add, div_le_iff₀ hα]; linarith
  have hβe : β = α * (1 + ε) := by rw [hε]; field_simp; ring
  have hs : 0 < 1 + ε := by linarith
  have hpi := Real.pi_pos
  unfold statDist
  rw [RLP_scale _ α hα]
  have hpt : ∀ y : ℝ, ENNReal.ofReal α * ENNReal.ofReal |nu α (α * y) - nu β (α * y)| =
      ENNReal.ofReal |Real.exp (-Real.pi * y ^ 2) -
        1 / (1 + ε) * Real.exp (-Real.pi * y ^ 2 / (1 + ε) ^ 2)| := by
    intro y
    rw [← ENNReal.ofReal_mul hα.le, ← abs_of_pos hα, ← abs_mul, abs_of_pos hα]
    congr 1
    have := RLP_nu_scaled α ε y hα hε0
    rw [← this]
    simp only [nu, hβe]
  simp_rw [hpt]
  obtain ⟨h1, h2, h3⟩ := RLP_first_display ε hε0 hε1
  obtain ⟨h4, h5⟩ := RLP_final_evaluation ε hε0 hε1
  refine h1.trans ?_
  rw [h2, h3]
  have hb : 0 < Real.pi / (1 + ε) ^ 2 := by positivity
  have hexp : ∀ x : ℝ, Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2) =
      Real.exp (-(Real.pi / (1 + ε) ^ 2) * x ^ 2) := fun x => by congr 1; ring
  have hint : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) := by
    simp_rw [hexp]
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
    simpa [Real.rpow_two] using this
  have hnn : ∀ x : ℝ, 0 ≤ 2 * Real.pi * ε * (x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) :=
    fun x => by positivity
  have hI : ENNReal.ofReal (2 * Real.pi * ε * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) =
      ∫⁻ x : ℝ, ENNReal.ofReal (2 * Real.pi * ε *
        (x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2))) := by
    rw [← integral_const_mul]
    exact ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (Filter.Eventually.of_forall hnn)
  have hle : ∫⁻ x : ℝ, ENNReal.ofReal
        (|Real.exp (-Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2) - 1| *
          Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi * ε * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) := by
    rw [hI]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have hc : 0 < Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2) := Real.exp_pos _
    have hq : 1 - 1 / (1 + ε) ^ 2 ≤ 2 * ε := by
      have : 1 - 2 * ε ≤ 1 / (1 + ε) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ε, pow_pos hε0 3]
      linarith
    have ht0 : 0 ≤ Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2 := by
      have : 1 / (1 + ε) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have : 0 ≤ 1 - 1 / (1 + ε) ^ 2 := by linarith
      positivity
    have h6 : |Real.exp (-Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2) - 1| ≤
        Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2 := by
      have hE1 : Real.exp (-Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      rw [abs_of_nonpos (by linarith), neg_sub]
      have := Real.one_sub_le_exp_neg (Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2)
      have e : -(Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2) =
          -Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2 := by ring
      rw [e] at this
      linarith
    have h7 : Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2 ≤ 2 * Real.pi * ε * x ^ 2 := by
      have : Real.pi * (1 - 1 / (1 + ε) ^ 2) ≤ Real.pi * (2 * ε) :=
        mul_le_mul_of_nonneg_left hq hpi.le
      nlinarith [sq_nonneg x]
    calc |Real.exp (-Real.pi * (1 - 1 / (1 + ε) ^ 2) * x ^ 2) - 1| *
          Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)
        ≤ (2 * Real.pi * ε * x ^ 2) * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2) :=
          mul_le_mul_of_nonneg_right (h6.trans h7) hc.le
      _ = _ := by ring
  have hmain : ENNReal.ofReal (2 * Real.pi * ε * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2)) +
      ENNReal.ofReal ε ≤ ENNReal.ofReal (9 * ε) := by
    rw [← ENNReal.ofReal_add (by
      have : 0 ≤ ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ε) ^ 2) :=
        integral_nonneg fun x => by positivity
      positivity) hε0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [h4, h5]
  calc _ ≤ _ := add_le_add hle le_rfl
    _ ≤ _ := hmain
