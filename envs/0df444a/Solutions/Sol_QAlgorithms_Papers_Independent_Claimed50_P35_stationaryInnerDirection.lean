-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.stationaryInnerDirection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:45:28.789112+00:00
-- url     : https://prove2.me/submissions/172dfac3-7bde-4e79-a2aa-4f8b6c51bd7b

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

/-- Appendix A, (1.2), p.11: an inner direction at a global minimum has
zero existing TWO-SIDED derivative. A single stationary line is not sufficient
for a global minimum. -/
theorem solution {I : Type} [Nonempty I]
    (F : Matrix I I ℂ → ℝ) (hconvex : ConvexOn ℝ {X | IsDensity X} F)
    (rho sigma : State I)
    (hmin : ∀ tau : State I, F rho.coefficients ≤ F tau.coefficients)
    (hinner : ∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Set.Ioo (-eta) eta,
      IsDensity (densityLine rho.coefficients sigma.coefficients t))
    (d : ℝ) (hd : HasDerivAt
      (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t)) d 0) :
    d = 0 := by
  obtain ⟨eta, heta, hline⟩ := hinner
  have hmin' : IsLocalMin (fun t : ℝ => F (densityLine rho.coefficients sigma.coefficients t)) 0 := by
    have hU : Set.Ioo (-eta) eta ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) heta
    filter_upwards [hU] with t ht
    have h0 : densityLine rho.coefficients sigma.coefficients 0 = rho.coefficients := by
      simp [densityLine]
    rw [h0]
    exact hmin ⟨_, hline t ht⟩
  exact hmin'.hasDerivAt_eq_zero hd



end
