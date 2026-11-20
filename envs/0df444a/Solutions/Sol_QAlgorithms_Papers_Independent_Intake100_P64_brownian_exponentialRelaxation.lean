-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.brownian_exponentialRelaxation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:26:26.446798+00:00
-- url     : https://prove2.me/submissions/40b6bd6c-db27-4726-8d72-1cb140580514

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

theorem AuxBER_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    (hc : ContinuousOn g (Set.Ici 0))
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt g 0 (Set.Ici 0) t) :
    ∀ t, 0 ≤ t → g t = g 0 := by
  intro t ht
  exact constant_of_has_deriv_right_zero (hc.mono Set.Icc_subset_Ici_self)
    (fun x hx => (hd x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) t ⟨ht, le_rfl⟩

theorem _root_.solution (a : GasTracerParameters) (beta sigmaTotal : ℝ)
    (hbeta : 0 < beta) (hsigma : 0 ≤ sigmaTotal)
    (p : ℝ → Momentum) (e : ℝ → ℝ)
    (hsol : BrownianMomentSolution (brownianFriction a beta sigmaTotal) beta p e) :
    ∀ t : ℝ, 0 ≤ t →
      p t = Real.exp (-brownianFriction a beta sigmaTotal * t) • p 0 ∧
      e t = 3 / (2 * beta) + (e 0 - 3 / (2 * beta)) *
        Real.exp (-2 * brownianFriction a beta sigmaTotal * t) ∧
      ‖(a.M * thermalSpeed a beta)⁻¹ • p t‖ ^ 2 =
        ‖(a.M * thermalSpeed a beta)⁻¹ • p 0‖ ^ 2 *
          Real.exp (-2 * brownianFriction a beta sigmaTotal * t) ∧
      2 * e t / (a.M * thermalSpeed a beta ^ 2) = 3 * a.m / (2 * a.M) +
        (2 * e 0 / (a.M * thermalSpeed a beta ^ 2) - 3 * a.m / (2 * a.M)) *
          Real.exp (-2 * brownianFriction a beta sigmaTotal * t) := by
  set η := brownianFriction a beta sigmaTotal with hη
  obtain ⟨hpc, hec, hpd, hed⟩ := hsol
  set k : ℝ := 3 / (2 * beta) with hk
  have hp : ∀ t, 0 ≤ t → Real.exp (η * t) • p t = p 0 := by
    have := AuxBER_const (g := fun t => Real.exp (η * t) • p t)
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).smul hpc)
      (fun t ht => by
        have h1 : HasDerivWithinAt (fun t => Real.exp (η * t)) (Real.exp (η * t) * η)
            (Set.Ici 0) t := by
          have := ((hasDerivAt_id t).const_mul η).exp
          simpa using this.hasDerivWithinAt
        have h2 := h1.smul (hpd t ht)
        refine h2.congr_deriv ?_
        rw [smul_smul, ← add_smul]
        convert zero_smul ℝ (p t) using 2; ring)
    intro t ht; simpa using this t ht
  have he : ∀ t, 0 ≤ t → Real.exp (2 * η * t) * (e t - k) = e 0 - k := by
    have := AuxBER_const (g := fun t => Real.exp (2 * η * t) * (e t - k))
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hec.sub continuousOn_const))
      (fun t ht => by
        have h1 : HasDerivWithinAt (fun t => Real.exp (2 * η * t)) (Real.exp (2 * η * t) * (2 * η))
            (Set.Ici 0) t := by
          have := ((hasDerivAt_id t).const_mul (2 * η)).exp
          simpa using this.hasDerivWithinAt
        have h2 := h1.mul ((hed t ht).sub_const k)
        exact h2.congr_deriv (by ring))
    intro t ht; simpa using this t ht
  intro t ht
  have hpt : p t = Real.exp (-η * t) • p 0 := by
    rw [← hp t ht, smul_smul, ← Real.exp_add]; simp
  have het : e t = k + (e 0 - k) * Real.exp (-2 * η * t) := by
    have h := he t ht
    have hx : Real.exp (-2 * η * t) * Real.exp (2 * η * t) = 1 := by
      rw [← Real.exp_add]; simp
    have : e t - k = (e 0 - k) * Real.exp (-2 * η * t) := by
      rw [← h]; linear_combination -(e t - k) * hx
    linarith
  have hexp : Real.exp (-η * t) ^ 2 = Real.exp (-2 * η * t) := by
    rw [← Real.exp_nat_mul]; ring_nf
  refine ⟨hpt, het, ?_, ?_⟩
  · rw [hpt, smul_comm, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      hexp, mul_comm]
  · have hv : thermalSpeed a beta ^ 2 = 2 / (beta * a.m) := by
      rw [thermalSpeed, Real.sq_sqrt (by have := a.m_pos; positivity)]
    have hm := a.m_pos
    have hM := a.M_pos
    rw [hv, het, hk]
    field_simp

end QAlgorithms.Papers.Independent.Intake100.P64

end
