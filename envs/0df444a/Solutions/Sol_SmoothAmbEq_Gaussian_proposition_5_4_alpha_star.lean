-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.proposition_5_4_alpha_star
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:05:57.968433+00:00
-- url     : https://prove2.me/submissions/cd369462-520d-4ab8-9aae-ea3b5e4dccdf

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SAEAlpha

/-- The integrand of (5.17). -/
noncomputable def g (a x : ℝ) : ℝ := Real.exp (-x) * (1 + (1 - a) * x) ^ (a / (1 - a))

/-- The integral of (5.17). -/
noncomputable def F (a : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), g a x

lemma base_ge_one {a x : ℝ} (ha : a ≤ 0) (hx : 0 ≤ x) : 1 ≤ 1 + (1 - a) * x := by
  have : 0 ≤ (1 - a) * x := mul_nonneg (by linarith) hx
  linarith

lemma expo_nonpos {a : ℝ} (ha : a ≤ 0) : a / (1 - a) ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg ha (by linarith)

lemma g_pos {a x : ℝ} (ha : a ≤ 0) (hx : 0 ≤ x) : 0 < g a x := by
  unfold g
  have := base_ge_one ha hx
  positivity

lemma g_le {a x : ℝ} (ha : a ≤ 0) (hx : 0 ≤ x) : g a x ≤ Real.exp (-x) := by
  unfold g
  have h1 : (1 + (1 - a) * x) ^ (a / (1 - a)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one ha hx) (expo_nonpos ha)
  have := Real.exp_pos (-x)
  nlinarith

lemma g_meas (a : ℝ) : Measurable (g a) := by
  unfold g; fun_prop

lemma g_integrable {a : ℝ} (ha : a ≤ 0) : IntegrableOn (g a) (Ioi 0) := by
  refine (integrableOn_exp_neg_Ioi 0).mono' (g_meas a).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (g_pos ha (le_of_lt hx))]
  exact g_le ha (le_of_lt hx)

lemma g_strictMono {a a' x : ℝ} (haa : a < a') (ha' : a' ≤ 0) (hx : 0 < x) :
    g a x < g a' x := by
  unfold g
  apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
  have hB : 1 < 1 + (1 - a') * x := by
    have : 0 < (1 - a') * x := mul_pos (by linarith) hx
    linarith
  have hBB : 1 + (1 - a') * x < 1 + (1 - a) * x := by nlinarith
  have hB0 : 0 < 1 + (1 - a) * x := by linarith
  rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_lt_exp.2
  have hL' : 0 < Real.log (1 + (1 - a') * x) := Real.log_pos hB
  have hLL : Real.log (1 + (1 - a') * x) < Real.log (1 + (1 - a) * x) :=
    Real.log_lt_log (by linarith) hBB
  have he : a / (1 - a) < a' / (1 - a') := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have he0 : a / (1 - a) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  calc Real.log (1 + (1 - a) * x) * (a / (1 - a))
      < Real.log (1 + (1 - a') * x) * (a / (1 - a)) := mul_lt_mul_of_neg_right hLL he0
    _ < Real.log (1 + (1 - a') * x) * (a' / (1 - a')) := mul_lt_mul_of_pos_left he hL'

lemma F_strictMono {a a' : ℝ} (haa : a < a') (ha' : a' ≤ 0) : F a < F a' := by
  unfold F
  rw [← sub_pos, ← integral_sub (g_integrable ha') (g_integrable (by linarith))]
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun x => g a' x - g a x) ∩ Ioi 0 = Ioi 0 := by
      ext x
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨(sub_pos.2 (g_strictMono haa ha' hx)).ne', hx⟩
    rw [this]; simp
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
    exact (sub_pos.2 (g_strictMono haa ha' hx)).le
  · exact (g_integrable ha').sub (g_integrable (by linarith))

lemma F_zero : F 0 = 1 := by
  unfold F g
  simp only [sub_zero, zero_div, Real.rpow_zero, mul_one]
  exact integral_exp_neg_Ioi_zero

lemma F_continuousOn : ContinuousOn F (Iic 0) := by
  unfold F
  apply continuousOn_of_dominated (bound := fun x => Real.exp (-x))
  · intro a _; exact (g_meas a).aestronglyMeasurable
  · intro a ha
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (g_pos ha (le_of_lt hx))]
    exact g_le ha (le_of_lt hx)
  · exact integrableOn_exp_neg_Ioi 0
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
    unfold g
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow (by fun_prop)
    · apply ContinuousOn.div continuousOn_id (by fun_prop)
      intro a ha
      have : a ≤ 0 := ha
      linarith
    · intro a ha
      exact Or.inl (by have := base_ge_one ha (le_of_lt hx); linarith)

lemma F_upper {a : ℝ} (ha : a ≤ -1) :
    F a ≤ (1 - a) ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
  rw [Real.Gamma_eq_integral (by norm_num), ← integral_const_mul]
  unfold F
  have hint : IntegrableOn (fun x => (1 - a) ^ (-(1 / 2 : ℝ)) *
      (Real.exp (-x) * x ^ ((1 / 2 : ℝ) - 1))) (Ioi 0) :=
    (Real.GammaIntegral_convergent (by norm_num)).const_mul _
  refine setIntegral_mono_on (g_integrable (by linarith)) hint measurableSet_Ioi ?_
  intro x hx
  have hx : 0 < x := hx
  unfold g
  have hB1 := base_ge_one (a := a) (by linarith) hx.le
  have h1 : (1 + (1 - a) * x) ^ (a / (1 - a)) ≤ (1 + (1 - a) * x) ^ (-(1 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hB1
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : (1 + (1 - a) * x) ^ (-(1 / 2 : ℝ)) ≤ ((1 - a) * x) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos (by linarith) hx) (by linarith) (by norm_num)
  have h3 : ((1 - a) * x) ^ (-(1 / 2 : ℝ)) = (1 - a) ^ (-(1 / 2 : ℝ)) * x ^ ((1 / 2 : ℝ) - 1) := by
    rw [Real.mul_rpow (by linarith) hx.le]; norm_num
  have := Real.exp_pos (-x)
  calc Real.exp (-x) * (1 + (1 - a) * x) ^ (a / (1 - a))
      ≤ Real.exp (-x) * ((1 - a) * x) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) this.le
    _ = _ := by rw [h3]; ring

end SAEAlpha

open SmoothAmbEq.Gaussian SAEAlpha

theorem solution (M : Model) : ∃! a : ℝ, IsAlphaStar M a := by
  set K : ℝ := M.σ ^ 2 / (M.σ₀ ^ 2 * M.T) with hK
  have hKpos : 0 < K := by
    have := M.hσ; have := M.hσ₀; have := M.hT; positivity
  have hIs : ∀ a, IsAlphaStar M a ↔ a < 0 ∧ (1 + K) * F a = 1 := by
    intro a; rfl
  set G : ℝ → ℝ := fun a => (1 + K) * F a with hG
  have hGc : ContinuousOn G (Iic 0) := continuousOn_const.mul F_continuousOn
  have hG0 : G 0 = 1 + K := by simp [hG, F_zero]
  -- a point where G < 1
  set a₀ : ℝ := -(16 * (1 + K) ^ 2) with ha₀
  have ha₀le : a₀ ≤ -1 := by rw [ha₀]; nlinarith
  have hGa₀ : G a₀ < 1 := by
    have hF := F_upper ha₀le
    have hgam : Real.Gamma (1 / 2) ≤ 2 := by
      rw [Real.Gamma_one_half_eq]
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt Real.pi_le_four
    have hpow : (1 - a₀) ^ (-(1 / 2 : ℝ)) ≤ (4 * (1 + K))⁻¹ := by
      have e : (4 * (1 + K))⁻¹ = (16 * (1 + K) ^ 2) ^ (-(1 / 2 : ℝ)) := by
        rw [show (16 * (1 + K) ^ 2) = (4 * (1 + K)) ^ (2 : ℝ) by
          rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one]
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [ha₀]; linarith) (by norm_num)
    have hFpos : 0 ≤ (1 - a₀) ^ (-(1 / 2 : ℝ)) := by
      apply Real.rpow_nonneg; linarith
    have hFa : F a₀ ≤ (4 * (1 + K))⁻¹ * 2 := by
      refine hF.trans ?_
      exact mul_le_mul hpow hgam (Real.Gamma_pos_of_pos (by norm_num)).le (by positivity)
    have : (1 + K) * ((4 * (1 + K))⁻¹ * 2) = 1 / 2 := by field_simp; ring
    simp only [hG]
    nlinarith
  -- existence by the intermediate value theorem
  have ha₀neg : a₀ < 0 := by linarith
  have hsub : Icc (G a₀) (G 0) ⊆ G '' Icc a₀ 0 :=
    intermediate_value_Icc ha₀neg.le (hGc.mono fun x hx => hx.2)
  obtain ⟨c, hc, hGc1⟩ := hsub ⟨hGa₀.le, by rw [hG0]; linarith⟩
  have hc0 : c < 0 := by
    rcases hc.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, hG0] at hGc1; linarith
  refine ⟨c, (hIs c).2 ⟨hc0, hGc1⟩, fun a ha => ?_⟩
  obtain ⟨ha0, haG⟩ := (hIs a).1 ha
  have hG_sm : ∀ x y : ℝ, x < y → y ≤ 0 → G x < G y := fun x y hxy hy =>
    mul_lt_mul_of_pos_left (F_strictMono hxy hy) (by linarith)
  rcases lt_trichotomy a c with h | h | h
  · have := hG_sm a c h hc0.le
    simp only [hG] at this hGc1
    linarith
  · exact h
  · have := hG_sm c a h ha0.le
    simp only [hG] at this hGc1
    linarith
