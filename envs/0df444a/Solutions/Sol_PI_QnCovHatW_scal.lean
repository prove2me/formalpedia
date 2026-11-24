-- Prove2me | solution 1 for PI.QnCovHatW.scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:08:00.455502+00:00
-- url     : https://prove2.me/submissions/eaf780c5-769b-467b-858b-5c63d220c867

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution {m : ℕ} (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hPQ : P * Q = 1)
    (a β : Fin (m + 1) → ℂ) (i' j' : Fin (m + 1)) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β ᵥ* P) i * (Q *ᵥ a) j) *
          ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
  have hsign : ∀ i j : Fin (m + 1), ((-1 : ℂ)) ^ ((i : ℕ) + (j : ℕ)) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) := by
    intro i j
    rw [← pow_add, ← pow_add]
    have h : (i' : ℕ) + j' + ((i' : ℕ) + i + ((j : ℕ) + j')) = ((i : ℕ) + j) + 2 * ((i' : ℕ) + j') := by ring
    rw [h, pow_add (-1 : ℂ) ((i : ℕ) + (j : ℕ)), pow_mul]
    norm_num
  have hX : ∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
      (P.submatrix i'.succAbove i.succAbove).det) = P.det * β i' := by
    have h1 : ∀ i : Fin (m + 1), (-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
        (P.submatrix i'.succAbove i.succAbove).det = P.adjugate i i' :=
      fun i => (Matrix.adjugate_fin_succ_eq_det_submatrix P i i').symm
    simp_rw [h1]
    have h2 : ∑ i, (β ᵥ* P) i * P.adjugate i i' = (β ᵥ* P ᵥ* P.adjugate) i' := rfl
    rw [h2, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    first
    | (rw [Matrix.vecMul_smul, Matrix.vecMul_one]; rfl)
    | simp [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm]
  have hY : ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
      (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j = Q.det * a j' := by
    have h1 : ∀ j : Fin (m + 1), (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
        (Q.submatrix j.succAbove j'.succAbove).det = Q.adjugate j' j :=
      fun j => (Matrix.adjugate_fin_succ_eq_det_submatrix Q j' j).symm
    simp_rw [h1]
    have h2 : ∑ j, Q.adjugate j' j * (Q *ᵥ a) j = (Q.adjugate *ᵥ (Q *ᵥ a)) j' := rfl
    rw [h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    first
    | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
    | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  calc _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) *
        ((∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
          (P.submatrix i'.succAbove i.succAbove).det)) *
        (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
          (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsign i j]
        ring
    _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
        rw [hX, hY]
        linear_combination (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' * hdet
end PI.QnCovHatW
