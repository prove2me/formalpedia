-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.convexMinimumCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:47:12.405258+00:00
-- url     : https://prove2.me/submissions/616729c0-85fb-4494-8315-ba6274c42815

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

section G68ILIB

end G68ILIB

/-- Appendix A, (1.1), p.11: all-density minimum criterion, with finite
right derivatives. No pure-direction reduction or derivative affinity is assumed. -/
theorem solution {I : Type} [Nonempty I]
    (F : Matrix I I ℂ → ℝ) (hconvex : ConvexOn ℝ {X | IsDensity X} F)
    (rho : State I) (d : State I → ℝ)
    (hd : ∀ sigma, HasDerivWithinAt
      (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t))
      (d sigma) (Set.Ici 0) 0) :
    (∀ sigma : State I, F rho.coefficients ≤ F sigma.coefficients) ↔
      ∀ sigma : State I, 0 ≤ d sigma := by
  have h0 : ∀ sigma : State I, densityLine rho.coefficients sigma.coefficients 0 = rho.coefficients := by
    intro sigma; simp [densityLine]
  have hmem : ∀ sigma : State I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      IsDensity (densityLine rho.coefficients sigma.coefficients t) := by
    intro sigma t ht0 ht1
    exact hconvex.1 rho.density sigma.density (by linarith) ht0 (by ring)
  have hslope : ∀ sigma : State I, Tendsto
      (slope (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t)) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (d sigma)) := by
    intro sigma
    have := hasDerivWithinAt_iff_tendsto_slope.1 (hd sigma).Ioi_of_Ici
    rwa [Set.sdiff_singleton_eq_self Set.self_notMem_Ioi] at this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 := by
    have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht using ht
  constructor
  · intro hmin sigma
    refine ge_of_tendsto (hslope sigma) ?_
    filter_upwards [hev] with t ht
    rw [slope_def_field, h0]
    apply div_nonneg _ (by linarith)
    have := hmin ⟨_, hmem sigma t ht.1.le ht.2.le⟩
    simp only at this
    linarith
  · intro hd0 sigma
    have hle : d sigma ≤ F sigma.coefficients - F rho.coefficients := by
      refine le_of_tendsto (hslope sigma) ?_
      filter_upwards [hev] with t ht
      rw [slope_def_field, h0, sub_zero, div_le_iff₀ ht.1]
      have := hconvex.2 rho.density sigma.density (show (0:ℝ) ≤ 1 - t by linarith) ht.1.le
        (show 1 - t + t = (1:ℝ) by ring)
      simp only [smul_eq_mul] at this
      unfold densityLine
      nlinarith
    linarith [hd0 sigma]



end
