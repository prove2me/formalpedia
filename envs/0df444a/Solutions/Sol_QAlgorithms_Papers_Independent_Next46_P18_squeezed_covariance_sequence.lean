-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.squeezed_covariance_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-20T17:10:30.243874+00:00
-- url     : https://prove2.me/submissions/84ee8909-7194-4a1a-b12b-640883eca18a

import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_isotropic_projection_decomposition
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_squeeze_projection_posSemidef

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction

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

open QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

theorem solution {s t : ℕ}
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (hisotropic : K.transpose * (physicalCommutationMatrix s 1) * K = 0) :
    ∃ gamma : ℕ → Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      (∀ n, quantumCovariance ((2 : ℝ) • gamma n)) ∧
      Tendsto (fun n => K.transpose * gamma n * K) atTop (𝓝 0) := by
  obtain ⟨P, Q, R, hPsym, hQsym, hRsym, hPid, hQid, hRid, hPQ, hPR, hQR,
    hsum, hQ, hPK, hQK, hRK⟩ := isotropic_projection_decomposition K hisotropic
  have hDelta : physicalCommutationMatrix s 1 =
      QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s := by
    ext i j
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    fin_cases i2 <;> fin_cases j2 <;>
      simp [physicalCommutationMatrix,
        QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm]
  have hQ' : Q = -(QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s) *
      P * (QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s) := by
    rw [hQ, hDelta]
  let gamma : ℕ → Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ := fun n =>
    (1 / 2 : ℝ) • ((1 / ((n + 1 : ℕ) : ℝ)) • P + ((n + 1 : ℕ) : ℝ) • Q + R)
  refine ⟨gamma, ?_, ?_⟩
  · intro n
    have hn : 0 < n + 1 := Nat.succ_pos n
    have h := squeeze_projection_posSemidef P Q R hPsym hQsym hRsym hPid hQid hRid
      hPQ hPR hQR hsum hQ' (n + 1) hn
    simpa [quantumCovariance, gamma, smul_smul, Matrix.map_add, Matrix.map_smul,
      Matrix.map_one, Matrix.map_mul] using h
  · have hcomp : ∀ n, K.transpose * gamma n * K =
        (1 / (2 * ((n + 1 : ℕ) : ℝ))) • (K.transpose * K) := by
      intro n
      simp only [gamma, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        hPK, hQK, hRK, smul_add, smul_smul, smul_zero, add_zero]
      congr 1
      field_simp
    have htend : Tendsto (fun n : ℕ => (1 / (2 * ((n + 1 : ℕ) : ℝ))) •
        (K.transpose * K)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
          (by norm_num : (0 : ℝ) < 2)
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
        h2.const_div_atTop 1
      simpa using h1.smul_const (K.transpose * K)
    exact htend.congr' (Eventually.of_forall fun n => (hcomp n).symm)

end
