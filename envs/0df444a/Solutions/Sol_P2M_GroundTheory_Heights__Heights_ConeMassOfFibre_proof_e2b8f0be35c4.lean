-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_proof_e2b8f0be35c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:59.037214+00:00
-- url     : https://prove2.me/submissions/3e2ae097-e3d6-4b84-a64f-a2e94bf616fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreCount_coordPlaneIdeal_b9fcb6704b37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_coordPlaneBlock_det_ne_zero_029df6309a2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeMassOfFibre
theorem _root_.solution (hA : ConeFibreAverage.Statement) : ConeMassOfFibre.Statement := by
  intro n m δ h J hJ hfib
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact coneMass_of_fibre_zero h J hJ hfib
  by_cases hmn : m ≤ n
  swap
  · have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
      rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 2 * n < 2 * m)
    rw [Real.hausdorffMeasure_of_finrank_lt hlt]
    simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨K, hK0, hKtop, hK⟩ := hA (m + k) m
  have hdet := ae_coordPlaneBlock_det_ne_zero m k
  have hL1 : ∀ᵐ π : Fin m → Fin (m + k) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m),
      fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = (1 : ℕ) := by
    filter_upwards [hdet] with π hπ
    exact Filter.Eventually.of_forall fun w => by
      rw [fibreCount_coordPlaneIdeal π hπ w]
      rfl
  have hC := hK h J hJ (by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ)
  have hL := hK (HermNorm.std (m + k)) (coordPlaneIdeal m k) (isProjPrime_coordPlaneIdeal hm k) (by
    filter_upwards [hL1] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top 1)
  rw [lintegral_matGauss_of_ae_eq δ _ hfib] at hC
  rw [lintegral_matGauss_of_ae_eq 1 _ hL1, Nat.cast_one, one_mul] at hL
  have hLset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧
      y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k)} =
      {y | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_coneSet_coordPlaneIdeal]
  rw [hLset] at hL
  rw [hL, ← mul_assoc, mul_comm (δ : ℝ≥0∞) K, mul_assoc] at hC
  exact ((ENNReal.mul_right_inj hK0.ne' hKtop.ne).1 hC).symm
end ConeMassOfFibre
end GroundTheory.Heights₂.Heights
