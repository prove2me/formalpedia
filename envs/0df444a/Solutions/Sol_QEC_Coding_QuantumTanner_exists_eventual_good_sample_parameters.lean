-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_good_sample_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:37:28.459524+00:00
-- url     : https://prove2.me/submissions/ec57d3fa-16cd-4340-8a91-b5e262fe5674

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_eventual_parameters_of_goodLocalCodeEvent
import Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_source_goodLocalCodeSample
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_cast_le
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_add_one
import Theorems.Thm_QEC_Coding_QuantumTanner_randomRowCount_lt_degree


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hDeltaHalf : delta < 1 / 2)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho Delta) A B,
        GoodLocalCodeEvent (randomRowCount rho Delta) (Delta - randomRowCount rho Delta)
          (Nat.ceil (delta * Delta))
          (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
          (Nat.floor ((Delta : ℝ) ^ gamma)) sample ∧
        ∀ (G : Type v) [Group G] [Fintype G]
          (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : Function.Injective L) (hR : Function.Injective R)
          (hLA : ∀ a, L (invA a) = (L a)⁻¹)
          (hRB : ∀ b, R (invB b) = (R b)⁻¹)
          (hTNC : ∀ g a b, L a * g ≠ g * R b),
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).leftCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).rightCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        let D := canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample
        0 < D.blockLength ∧ 0 < D.encodedDimension ∧
          ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
            (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
            delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
              (distance : ℝ) ∧
            QEC.Coding.BoundedLocality
              (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
              (Delta * Delta) := by
  obtain ⟨tSample, hSample⟩ := exists_eventual_source_goodLocalCodeSample
    epsilon gamma delta rho hEpsilon hEpsilonHalf hGammaLower hGammaUpper
    hDeltaDistance hDeltaHalf hRho hRhoHalf hEntropy
  obtain ⟨tDistance, hDistance⟩ := Data.exists_eventual_parameters_of_goodLocalCodeEvent
    delta epsilon gamma rho hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
    hRho.le hRhoHalf
  refine ⟨max tSample (max tDistance (max 1 (Nat.ceil (2 / rho)))), ?_⟩
  intro Delta hLarge A B _ _ hCardA hCardB
  have hSampleLarge : tSample ≤ Delta := (Nat.le_max_left _ _).trans hLarge
  have hRemaining := (Nat.le_max_right _ _).trans hLarge
  have hDistanceLarge : tDistance ≤ Delta := (Nat.le_max_left _ _).trans hRemaining
  have hNumerical := (Nat.le_max_right _ _).trans hRemaining
  have hDelta : 0 < Delta := by
    have := (Nat.le_max_left 1 _).trans hNumerical
    omega
  have hRowsPositive : 0 < randomRowCount rho Delta := by
    have hCeil := (Nat.le_max_right 1 _).trans hNumerical
    have hDiv : (2 : ℝ) / rho ≤ Delta := Nat.ceil_le.mp hCeil
    have hMul := (div_le_iff₀ hRho).mp hDiv
    have hFloor := randomRowCount_lt_add_one rho Delta
    have hPositive : (0 : ℝ) < randomRowCount rho Delta := by nlinarith
    exact_mod_cast hPositive
  have hRowsDelta := randomRowCount_lt_degree hRho.le (by linarith) hDelta
  obtain ⟨sample, hGood⟩ := hSample Delta hSampleLarge A B hCardA hCardB
  refine ⟨sample, hGood, ?_⟩
  intro G _ _ L R invA invB hL hR hLA hRB hTNC hLeft hRight
  exact hDistance Delta hDistanceLarge G A B (CayleySquare L R)
    (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
    (TensorBasisIndex (tensorCode sample.codeA sample.codeB))
    (canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample)
    (randomRowCount rho Delta) hRowsPositive hRowsDelta (randomRowCount_cast_le hRho.le)
    hCardA hCardB sample rfl rfl hGood
    (cayleySquareComplex_hasCayleyLinkIdentities L R invA invB hL hR hLA hRB hTNC)
    hLeft hRight
end QEC.Coding.QuantumTanner
