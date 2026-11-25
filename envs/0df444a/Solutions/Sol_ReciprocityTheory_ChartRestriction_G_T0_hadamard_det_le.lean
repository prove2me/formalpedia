-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:11.87594+00:00
-- url     : https://prove2.me/submissions/b765c0d3-f19d-4528-a8c2-b81b92def4e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_psd_det_re_le_prod_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped BigOperators ComplexOrder
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  have hdet : (A * Aᴴ).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [show star A.det = (starRingEnd ℂ) A.det from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hdiag : ∀ i, ((A * Aᴴ) i i).re = ∑ j, ‖A i j‖ ^ 2 := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have key := psd_det_re_le_prod_diag n (A * Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [hdet] at key
  simp only [hdiag] at key
  have hs : ∀ i, 0 ≤ ∑ j, ‖A i j‖ ^ 2 := fun i => Finset.sum_nonneg fun j _ => by positivity
  calc ‖A.det‖ = Real.sqrt (‖A.det‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← Finset.prod_pow]
        have h : ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) ^ 2 = ∏ i, ∑ j, ‖A i j‖ ^ 2 :=
          Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hs i)
        rw [h]
        exact key
    _ = ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) :=
        Real.sqrt_sq (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)
end ReciprocityTheory.ChartRestriction.G.T0
