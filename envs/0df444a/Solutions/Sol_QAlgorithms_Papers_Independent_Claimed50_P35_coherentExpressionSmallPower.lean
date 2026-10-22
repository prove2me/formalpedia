-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.coherentExpressionSmallPower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:00:11.01772+00:00
-- url     : https://prove2.me/submissions/8e7c9513-9f3e-4fbe-b972-5c74b9b13c61

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)


theorem g67v_deriv (v : ℝ) (hv : 0 < v) :
    HasDerivAt bosonicEntropy (Real.logb 2 ((v + 1) / v)) v := by
  have h1 := ((hasDerivAt_id' v).add_const 1).mul (((hasDerivAt_id' v).add_const 1).log (by linarith))
  have h2 := (hasDerivAt_id' v).mul (Real.hasDerivAt_log hv.ne')
  have h3 := (h1.sub h2).div_const (Real.log 2)
  have e : bosonicEntropy = fun x => ((x + 1) * Real.log (x + 1) - x * Real.log x) / Real.log 2 := by
    funext x; simp only [bosonicEntropy, Real.logb]; ring
  have h4 : HasDerivAt bosonicEntropy
      ((1 * Real.log (v + 1) + (v + 1) * (1 / (v + 1)) - (1 * Real.log v + v * v⁻¹)) / Real.log 2) v := by
    rw [e]; exact h3
  have hval : (1 * Real.log (v + 1) + (v + 1) * (1 / (v + 1)) - (1 * Real.log v + v * v⁻¹)) / Real.log 2 =
      Real.logb 2 ((v + 1) / v) := by
    show _ = Real.log ((v + 1) / v) / Real.log 2
    rw [Real.log_div (by linarith) hv.ne']
    have h5 : v + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval]; exact h4

theorem solution (k Nc : ℝ) (hk : 0 < k) (hNc : 0 ≤ Nc)
    (hv : 0 < vacuumOutput k Nc) :
    Tendsto (fun N : ℝ => coherentGaussianExpression N k Nc /
      (N * k ^ 2 * Real.logb 2 ((vacuumOutput k Nc + 1) / vacuumOutput k Nc)))
      (𝓝[>] 0) (𝓝 1) := by
  set v := vacuumOutput k Nc with hvdef
  set L := Real.logb 2 ((v + 1) / v) with hL
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by rw [one_lt_div hv]; linarith)
  have hd := g67v_deriv v hv
  have hs := hd.tendsto_slope_zero_right
  have hk2 : 0 < k ^ 2 := by positivity
  have hmap : Tendsto (fun N : ℝ => k ^ 2 * N) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun N : ℝ => k ^ 2 * N) (𝓝 0) (𝓝 (k ^ 2 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with N (hN : 0 < N)
      exact mul_pos hk2 hN
  have hlim := (hs.comp hmap).div_const L
  rw [div_self hL0.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N (hN : 0 < N)
  simp only [Function.comp, smul_eq_mul]
  unfold coherentGaussianExpression outputOccupation
  rw [← hvdef, add_comm (k ^ 2 * N) v]
  field_simp
