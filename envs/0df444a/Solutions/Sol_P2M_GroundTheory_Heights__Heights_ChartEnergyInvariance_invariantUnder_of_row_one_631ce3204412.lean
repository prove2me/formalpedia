-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_one_631ce3204412
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:03:05.180911+00:00
-- url     : https://prove2.me/submissions/0637ae80-16c8-4753-ac03-31ad2bd32cc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_row_zero_7bbe2f153d6a

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyInvariance
theorem _root_.solution (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by
  have h01 : (0 : Fin (e + 1 + 1)) ≠ 1 := by simp
  set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef
  have hSinv : EnergyInvariantUnder S := fun M N hM hN k => hS e M N hM hN k
  have hSdet : S.det ≠ 0 := by
    rw [hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]
    norm_num
  set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef
  have hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0 := fun j => by
    rw [hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hTdet : T.det = C 0 1 := by
    have hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0 := by
      funext p
      simp [Finset.sum_apply, Matrix.one_apply]
    have h := det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)
    rw [hrow] at h
    simpa using h
  have hTdet' : T.det ≠ 0 := by rw [hTdet]; exact h1
  have hST0 : ∀ m, C 0 m = (S * T) 0 m := fun m => by
    rw [hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef,
      updateRow_self]
  have hSTdet : (S * T).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hSdet hTdet'
  have hU : IsUnit (S * T).det := isUnit_iff_ne_zero.mpr hSTdet
  set A := C * (S * T)⁻¹ with hAdef
  have hCA : C = A * (S * T) := by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]
  have hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0 := fun j => by
    rw [hAdef, mul_apply]
    simp_rw [hST0]
    rw [← mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hAdet : A.det ≠ 0 := fun h => hC (by rw [hCA, det_mul, h, zero_mul])
  have h := invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet)
    (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet
  rwa [← hCA] at h
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
