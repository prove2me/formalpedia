-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.two_dimensional_minimal_noise_capacity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T02:52:39.916974+00:00
-- url     : https://prove2.me/submissions/a7315d30-befb-4a6d-acf3-864032161b5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_gaussian_cq_criterion
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_compatible_constraint_no_gain
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_vacuum_minimal_noise
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_two_dimensional_vacuum_supremum

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

private lemma kTwo_isotropic :
    kTwo.transpose * physicalCommutationMatrix 2 1 * kTwo = 0 := by
  ext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i2 <;> fin_cases j2 <;>
    simp [kTwo, physicalCommutationMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

private def kTwoRightInverse : Matrix (QuadratureIndex 2) (QuadratureIndex 1) ℝ :=
  fun i j => if i.2 = 0 then (if i.1.val = j.2.val then 1 else 0) else 0

private lemma kTwo_transpose_mul_rightInverse :
    kTwo.transpose * kTwoRightInverse = 1 := by
  ext i j
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases j1 <;> fin_cases i2 <;> fin_cases j2 <;>
    simp [kTwo, kTwoRightInverse, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma kTwo_transpose_surjective :
    Function.Surjective kTwo.transpose.mulVec := by
  intro y
  refine ⟨kTwoRightInverse.mulVec y, ?_⟩
  rw [Matrix.mulVec_mulVec y kTwo.transpose kTwoRightInverse,
    kTwo_transpose_mul_rightInverse, Matrix.one_mulVec]

private lemma half_one_posDef :
    ((1 / 2 : ℝ) • (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)).PosDef := by
  exact Matrix.PosDef.smul Matrix.PosDef.one (by norm_num : (0 : ℝ) < 1 / 2)

end QAlgorithms.Papers.Independent.Next46.P18

open QAlgorithms.Papers.Independent.Next46.P18

theorem solution {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 2 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J)
    (hG : GaussianChannel WA WB Phi kTwo ((1 / 2 : ℝ) • 1))
    (E : ℝ) (hE : 0 < E) :
    (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)).form =
      quadraticRaw WA kTwo ((1 / 2 : ℝ) • 1) ∧
    operationalAssistedCapacity Phi.predual.val
      (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E =
      regularizedUnassistedCapacity Phi.predual.val
        (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E ∧
    regularizedUnassistedCapacity Phi.predual.val
      (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E = ENNReal.ofReal (g E) := by
  have hcq : IsCQ Phi :=
    (gaussian_cq_criterion WA WB Phi kTwo ((1 / 2 : ℝ) • 1) hG).mpr
      (kTwo_isotropic)
  have hminimal : MinimalNoise ((1 / 2 : ℝ) •
      (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) :=
    vacuum_minimal_noise
  have hrank : Function.Surjective kTwo.transpose.mulVec :=
    kTwo_transpose_surjective
  have heps : ((1 / 2 : ℝ) •
      (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)).PosDef :=
    half_one_posDef
  have hprop := compatible_constraint_no_gain WA WB Phi kTwo ((1 / 2 : ℝ) • 1)
    hG hcq hminimal hrank ((1 / 2 : ℝ) • 1) heps E hE
  have hsup := two_dimensional_vacuum_supremum WA WB Phi hG E hE
  exact ⟨hprop.1, hprop.2.1.symm, hprop.2.1.trans (hprop.2.2.trans hsup)⟩

end
