-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.one_mode_gaussian_information
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T01:36:34.482263+00:00
-- url     : https://prove2.me/submissions/9b111d25-2e00-4a5b-bf51-d9a594484424
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_one_mode_gaussian_mutual_information
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_deltaOne_strictAntiOn_and_tendsto

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction
open scoped Matrix RealInnerProductSpace InnerProductSpace

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

private lemma deriv_g {x : ℝ} (hx : 0 < x) :
    deriv g x = Real.log (x + 1) - Real.log x := by
  unfold g
  have hx1 : x + 1 ≠ 0 := by positivity
  have h1 : deriv (fun y : ℝ => (y + 1) * Real.log (y + 1)) x =
      Real.log (x + 1) + 1 := by
    change deriv ((fun y : ℝ => y + 1) * (fun y : ℝ => Real.log (y + 1))) x =
      Real.log (x + 1) + 1
    rw [deriv_mul]
    · have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const 1
      have hlog : deriv (fun y : ℝ => Real.log (y + 1)) x = (x + 1)⁻¹ := by
        simpa using (hinner.log hx1).deriv
      rw [hlog]
      simp only [deriv_add_const, deriv_id'', one_mul]
      field_simp [hx1]
    · fun_prop
    · fun_prop
  have h2 : deriv (fun y : ℝ => y * Real.log y) x = Real.log x + 1 := by
    rw [Real.deriv_mul_log hx.ne']
  change deriv ((fun y : ℝ => (y + 1) * Real.log (y + 1)) -
    (fun y : ℝ => y * Real.log y)) x = Real.log (x + 1) - Real.log x
  rw [deriv_sub]
  · rw [h1, h2]
    ring
  · fun_prop
  · fun_prop

private lemma continuousOn_g : ContinuousOn g (Set.Ici (0 : ℝ)) := by
  unfold g
  fun_prop

private lemma strictMonoOn_g : StrictMonoOn g (Set.Ici (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) continuousOn_g ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [deriv_g hx]
  exact sub_pos.mpr (Real.log_lt_log hx (by linarith))

private lemma sqrt_one_div_four : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private lemma deltaOne_pos {E v P : ℝ} (hE : 0 < E) (hv : 0 < v)
    (hP : 1 / (4 * E) ≤ P) : 0 < deltaOne E v P := by
  unfold deltaOne
  apply sub_pos.mpr
  have h4E : 0 < 4 * E := by positivity
  have h1 : 1 ≤ P * (4 * E) := (div_le_iff₀ h4E).mp hP
  have hEP : (1 / 4 : ℝ) ≤ E * P := by nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (E * P) := by
    have := Real.sqrt_le_sqrt hEP
    rwa [sqrt_one_div_four] at this
  have hsecond : (0 : ℝ) ≤ Real.sqrt (E * P) - 1 / 2 := by linarith
  have hpos : 0 < E / (4 * v) := by positivity
  have hlt : Real.sqrt (E * P) - 1 / 2 < Real.sqrt (E * P + E / (4 * v)) - 1 / 2 := by
    have hlt0 : E * P < E * P + E / (4 * v) := by linarith
    have := Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ E * P) hlt0
    linarith
  have hfirst : (0 : ℝ) ≤ Real.sqrt (E * P + E / (4 * v)) - 1 / 2 := by linarith
  exact strictMonoOn_g hsecond hfirst hlt

private lemma deltaOne_endpoint {E v : ℝ} (hE : 0 < E) :
    deltaOne E v (1 / (4 * E)) = g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) := by
  unfold deltaOne
  have hE4 : E * (1 / (4 * E)) = 1 / 4 := by
    field_simp [hE.ne']
  rw [hE4]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := sqrt_one_div_four
  rw [hsqrt]
  have harg : (1 / 4 : ℝ) + E / (4 * v) = E / (4 * v) + 1 / 4 := by ring
  rw [harg]
  norm_num [g]

end QAlgorithms.Papers.Independent.Next46.P18

open QAlgorithms.Papers.Independent.Next46.P18

theorem solution {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 1 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J) (E v : ℝ) (hE : 0 < E) (hv : 0 < v)
    (hG : GaussianChannel WA WB Phi kOne (squeezedNoise v)) :
    (∀ (P : ℝ) (rho : State I), 1 / (4 * E) ≤ P →
      (∀ z, weylTraceCharacteristic WA rho.coefficients z =
        gaussianFunction 0 (diagonalCovariance 1 E P) z) →
      mutualInformation rho.coefficients Phi.predual.val < ⊤ ∧
      (mutualInformation rho.coefficients Phi.predual.val).toReal =
        g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) - deltaOne E v P) ∧
    (∀ P : ℝ, 1 / (4 * E) ≤ P → 0 < deltaOne E v P) ∧
    StrictAntiOn (deltaOne E v) (Set.Ici (1 / (4 * E))) ∧
    deltaOne E v (1 / (4 * E)) = g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) ∧
    Tendsto (deltaOne E v) atTop (𝓝 0) := by
  have hinfo := one_mode_gaussian_mutual_information WA WB Phi E v hE hv hG
  have hscalar := deltaOne_strictAntiOn_and_tendsto hE hv
  exact ⟨hinfo, fun P hP => deltaOne_pos hE hv hP, hscalar.1,
    deltaOne_endpoint hE, hscalar.2⟩

end
