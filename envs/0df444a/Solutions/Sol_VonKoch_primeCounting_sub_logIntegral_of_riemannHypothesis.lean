-- Prove2me | solution 1 for VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:37:34.605426+00:00
-- url     : https://prove2.me/submissions/5703c7bc-2118-41c1-b8c2-95d030a4cde2

import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
import Theorems.Thm_LandauExplore_theta_error_of_psi_error

set_option autoImplicit false

open Real intervalIntegral MeasureTheory Set

namespace VonKochAux

/-- Under RH, `θ(t) - t = O(√t log² t)` for `t ≥ 2`. -/
lemma theta_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ K * √t * (log t) ^ 2 := by
  obtain ⟨C, hC⟩ := LandauCriterion.psi_error_of_riemannHypothesis hRH
  have hpsi : LandauExplore.psiError C := fun x hx => hC x hx
  refine ⟨max C 0 + 4, by positivity, fun t ht => ?_⟩
  have h := LandauExplore.theta_error_of_psi_error hpsi ht
  have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog : (1 : ℝ) / 2 ≤ log t := le_trans hlog2 (Real.log_le_log (by norm_num) ht)
  have hsq : 0 ≤ √t := sqrt_nonneg t
  have h2 : 2 * log t ≤ 4 * (log t) ^ 2 := by nlinarith
  have h3 : C * (log t) ^ 2 ≤ max C 0 * (log t) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  calc |Chebyshev.theta t - t| ≤ (C * (log t) ^ 2 + 2 * log t) * √t := h
    _ ≤ (max C 0 * (log t) ^ 2 + 4 * (log t) ^ 2) * √t :=
        mul_le_mul_of_nonneg_right (by linarith) hsq
    _ = (max C 0 + 4) * √t * (log t) ^ 2 := by ring

lemma log_pos_of_two_le {t : ℝ} (ht : 2 ≤ t) : 0 < log t := Real.log_pos (by linarith)

lemma continuousOn_inv_log {x : ℝ} : ContinuousOn (fun t : ℝ => 1 / log t) (uIcc 2 x ∩ Ici 2) := by
  intro t ht
  have h2 : 2 ≤ t := ht.2
  have : log t ≠ 0 := (log_pos_of_two_le h2).ne'
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) this).continuousWithinAt

/-- Integration by parts for the logarithmic integral. -/
lemma li_parts {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / log t = x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / log t ^ 2 := by
  have hsub : uIcc (2 : ℝ) x ⊆ Ici 2 := by
    rw [uIcc_of_le hx]; exact Icc_subset_Ici_self
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) x,
      HasDerivAt (fun t => t / log t) (1 / log t - 1 / log t ^ 2) t := by
    intro t ht
    have h2 : 2 ≤ t := hsub ht
    have hlt : log t ≠ 0 := (log_pos_of_two_le h2).ne'
    have ht0 : t ≠ 0 := by linarith
    refine ((hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hlt).congr_deriv ?_
    field_simp
  have hc1 : ContinuousOn (fun t : ℝ => 1 / log t) (uIcc 2 x) := fun t ht => by
    have h2 : (2 : ℝ) ≤ t := hsub ht
    have hlt : log t ≠ 0 := (log_pos_of_two_le h2).ne'
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) hlt).continuousWithinAt
  have hc2 : ContinuousOn (fun t : ℝ => 1 / log t ^ 2) (uIcc 2 x) := fun t ht => by
    have h2 : (2 : ℝ) ≤ t := hsub ht
    have hlt : log t ^ 2 ≠ 0 := pow_ne_zero 2 (log_pos_of_two_le h2).ne'
    exact (continuousAt_const.div
      ((Real.continuousAt_log (by linarith)).pow 2) hlt).continuousWithinAt
  have hi1 := hc1.intervalIntegrable (μ := volume)
  have hi2 := hc2.intervalIntegrable (μ := volume)
  have hftc := integral_eq_sub_of_hasDerivAt hderiv (hi1.sub hi2)
  rw [integral_sub hi1 hi2] at hftc
  linarith

end VonKochAux

open VonKochAux in
theorem solution (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x := by
  obtain ⟨K, hK0, hK⟩ := theta_bound hRH
  refine ⟨3 * K + 3, fun x hx => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hsub : uIcc (2 : ℝ) x ⊆ Ici 2 := by
    rw [uIcc_of_le hx2]; exact Icc_subset_Ici_self
  have hlogx : 1 ≤ log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hsqx : 1 ≤ √x := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2, li_parts hx2]
  -- integrability facts
  have hi1 : IntervalIntegrable (fun t => Chebyshev.theta t / (t * log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) hx2).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hc2 : ContinuousOn (fun t : ℝ => 1 / log t ^ 2) (uIcc 2 x) := fun t ht => by
    have h2 : (2 : ℝ) ≤ t := hsub ht
    have hlt : log t ^ 2 ≠ 0 := pow_ne_zero 2 (log_pos_of_two_le h2).ne'
    exact (continuousAt_const.div
      ((Real.continuousAt_log (by linarith)).pow 2) hlt).continuousWithinAt
  have hi2 := hc2.intervalIntegrable (μ := volume)
  -- the difference of the two integrals
  have hdiff : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) -
      ∫ t in (2 : ℝ)..x, 1 / log t ^ 2 =
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2) := by
    rw [← integral_sub hi1 hi2]
    refine integral_congr fun t ht => ?_
    have h2 : 2 ≤ t := hsub ht
    have ht0 : t ≠ 0 := by linarith
    have hlt : log t ≠ 0 := (log_pos_of_two_le h2).ne'
    field_simp
  -- bound on the integral
  have hint_bound : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2)| ≤ 2 * K * √x := by
    have hg : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) volume 2 x := by
      refine (ContinuousOn.intervalIntegrable (μ := volume) ?_)
      intro t ht
      have h2 : (2 : ℝ) ≤ t := hsub ht
      exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith)))).continuousWithinAt
    have hle := norm_integral_le_of_norm_le hx2
      (f := fun t : ℝ => (Chebyshev.theta t - t) / (t * log t ^ 2))
      (g := fun t : ℝ => K * t ^ (-(1 / 2 : ℝ)))
      (Filter.Eventually.of_forall fun t ht => by
        have h2 : 2 ≤ t := le_of_lt ht.1
        have htpos : 0 < t := by linarith
        have hlt : 0 < log t := log_pos_of_two_le h2
        show ‖(Chebyshev.theta t - t) / (t * log t ^ 2)‖ ≤ K * t ^ (-(1 / 2 : ℝ))
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < t * log t ^ 2)]
        have hb := hK t h2
        have hid : K * √t * log t ^ 2 / (t * log t ^ 2) = K * t ^ (-(1 / 2 : ℝ)) := by
          have hs : 0 < √t := Real.sqrt_pos.mpr htpos
          rw [Real.rpow_neg htpos.le, ← Real.sqrt_eq_rpow]
          have hL : log t ^ 2 ≠ 0 := by positivity
          field_simp
          rw [Real.sq_sqrt htpos.le]
        rw [← hid]
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr hb) hg
    have hval : ∫ t in (2 : ℝ)..x, K * t ^ (-(1 / 2 : ℝ)) = K * ((x ^ (1 / 2 : ℝ) - 2 ^ (1 / 2 : ℝ)) / (1 / 2)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      norm_num
    rw [Real.norm_eq_abs, hval] at hle
    have h2pos : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hxs : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
    rw [hxs] at hle
    nlinarith
  have hfirst : |(Chebyshev.theta x - x) / log x| ≤ K * √x * log x := by
    have hlpos : 0 < log x := by linarith
    rw [abs_div, abs_of_pos hlpos, div_le_iff₀ hlpos]
    have := hK x hx2
    nlinarith
  have hlog2 : 2 / log 2 ≤ 3 := by
    have := Real.log_two_gt_d9
    rw [div_le_iff₀ (by linarith)]; linarith
  have hlog2pos : 0 < 2 / log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hexpr : Chebyshev.theta x / log x + (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * log t ^ 2)) -
      (x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / log t ^ 2) =
      (Chebyshev.theta x - x) / log x +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2)) + 2 / log 2 := by
    rw [← hdiff]; ring
  rw [hexpr]
  have hsx : 0 ≤ √x := Real.sqrt_nonneg x
  calc |(Chebyshev.theta x - x) / log x +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2)) + 2 / log 2|
      ≤ |(Chebyshev.theta x - x) / log x| +
        |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * log t ^ 2)| + |2 / log 2| :=
        abs_add_three _ _ _
    _ ≤ K * √x * log x + 2 * K * √x + 3 := by
        rw [abs_of_pos hlog2pos]; linarith
    _ ≤ (3 * K + 3) * √x * log x := by
        have h1 : 2 * K * √x ≤ 2 * K * √x * log x := by
          have := mul_le_mul_of_nonneg_left hlogx (by positivity : 0 ≤ 2 * K * √x)
          linarith
        have h2 : (3 : ℝ) ≤ 3 * √x * log x := by nlinarith
        nlinarith
