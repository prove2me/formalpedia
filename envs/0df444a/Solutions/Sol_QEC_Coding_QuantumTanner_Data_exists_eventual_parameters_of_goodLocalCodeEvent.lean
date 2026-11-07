-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.exists_eventual_parameters_of_goodLocalCodeEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:34:48.051214+00:00
-- url     : https://prove2.me/submissions/8dab85f8-3f1c-4f97-954f-aa5513a5e5f9

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_minimumDistance_of_dimension_pos
import Theorems.Thm_QEC_Coding_QuantumTanner_minimumDistance_ge_of_ceil_lower_bound
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_boundedLocality_degreeSquared
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_minimumDistance_ge_of_cayley_spectral
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_minimumDistance_of_encodedDimension_pos
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_source_rate_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_IsRobustWithPunctureResistance_isRobust
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_card_group_mul_local_degree_eq_twice_card_square


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v
open QEC.Coding.QuantumTanner.Data
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis) (r : Nat), 0 < r → r < Delta →
      (r : ℝ) ≤ rho * Delta →
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∀ (sample : RandomLocalCodeSample r A B),
      D.codeA = sample.codeA → D.codeB = sample.codeB →
      GoodLocalCodeEvent r (Delta - r) (Nat.ceil (delta * Delta))
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) sample →
      D.complex.HasCayleyLinkIdentities →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      0 < D.blockLength ∧ 0 < D.encodedDimension ∧
      ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
        (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
        delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
          (distance : ℝ) ∧
        QEC.Coding.BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
          (Delta * Delta) := by
  obtain ⟨t, ht⟩ := exists_eventual_minimumDistance_ge_of_cayley_spectral
    delta epsilon gamma hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  refine ⟨t, ?_⟩
  intro Delta hLarge G A B Square XBasis ZBasis _ _ _ _ _ _ _ D r hrPositive hrDelta
    hRowRate hCardA hCardB sample hCodeA hCodeB hGood hX hLeft hRight
  obtain ⟨hDimA, hDimB, hLowerA, hLowerB, hLowerADual, hLowerBDual,
    hPunctures, hPuncturesDual⟩ := hGood
  rw [← hCodeA] at hDimA hLowerA hLowerADual
  rw [← hCodeB] at hDimB hLowerB hLowerBDual
  rw [← hCodeA, ← hCodeB] at hPunctures hPuncturesDual
  have hDelta : 0 < Delta := hrPositive.trans hrDelta
  have hDimAPositive : 0 < Dimension D.codeA := by omega
  have hDimBPositive : 0 < Dimension D.codeB := by omega
  have hDimADual : Dimension D.codeA.dual = Delta - r := by
    rw [LinearCode.dual_dimension_eq_length_sub_dimension, Length, hCardA, hDimA]
  have hDimBDual : Dimension D.codeB.dual = r := by
    rw [LinearCode.dual_dimension_eq_length_sub_dimension, Length, hCardB, hDimB,
      Nat.sub_sub_self hrDelta.le]
  obtain ⟨dA, hdA⟩ := exists_minimumDistance_of_dimension_pos D.codeA hDimAPositive
  obtain ⟨dB, hdB⟩ := exists_minimumDistance_of_dimension_pos D.codeB hDimBPositive
  obtain ⟨dADual, hdADual⟩ := exists_minimumDistance_of_dimension_pos D.codeA.dual
    (by omega)
  obtain ⟨dBDual, hdBDual⟩ := exists_minimumDistance_of_dimension_pos D.codeB.dual
    (by omega)
  have hRate := D.source_rate_bound Delta r rho hDelta hCardA hCardB hrDelta.le
    hRho hRhoHalf hRowRate hDimA hDimB
  have hLength : 0 < D.blockLength := by
    have hCard := D.complex.card_group_mul_local_degree_eq_twice_card_square
    rw [hCardA, hCardB] at hCard
    rw [← Nat.mul_assoc] at hCard
    have hGroup : 0 < Fintype.card G := Fintype.card_pos
    have hProduct : 0 < Fintype.card G * Delta * Delta :=
      Nat.mul_pos (Nat.mul_pos hGroup hDelta) hDelta
    change 0 < Fintype.card Square
    omega
  have hDimension : 0 < D.encodedDimension := by
    have hLengthReal : 0 < (D.blockLength : ℝ) := by exact_mod_cast hLength
    have hFactor : 0 < (1 - 2 * rho) ^ 2 := sq_pos_of_pos (by linarith)
    have hDimensionReal := (mul_pos hFactor hLengthReal).trans_le hRate
    exact_mod_cast hDimensionReal
  obtain ⟨distance, hMinimum⟩ := D.exists_minimumDistance_of_encodedDimension_pos hDimension
  refine ⟨hLength, hDimension, distance, ⟨rfl, rfl, hMinimum⟩, hRate, ?_, ?_⟩
  · exact ht Delta hLarge G A B Square XBasis ZBasis D hX dA dB dADual dBDual
      hdA hdB hdADual hdBDual
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerA hdA)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerB hdB)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerADual hdADual)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerBDual hdBDual)
      hCardA hCardB hPunctures.isRobust hPuncturesDual.isRobust
      hPunctures hPuncturesDual hLeft hRight distance hMinimum
  · exact D.boundaryIncidence_boundedLocality_degreeSquared Delta r
      hCardA hCardB hrDelta.le hDimA hDimB
end QEC.Coding.QuantumTanner.Data
