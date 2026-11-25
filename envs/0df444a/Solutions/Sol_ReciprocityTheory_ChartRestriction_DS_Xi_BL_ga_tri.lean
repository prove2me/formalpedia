-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.ga_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:46.1818+00:00
-- url     : https://prove2.me/submissions/991c7f53-9a81-466c-8e2d-18291ec7f6a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sum_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_prod_Iic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_det_gram_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r : ℕ) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (l : Fin (r + 1)) :
    Ga k r l (fun a => ∑ b, τ b a • Z b) = (∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2) * Ga k r l Z := by
  have h : l.val + 1 ≤ r + 1 := by omega
  have hs : ∀ a : Fin (l.val + 1), (∑ b, τ b (Fin.castLE h a) • Z b) =
      ∑ j : Fin (l.val + 1), τ (Fin.castLE h j) (Fin.castLE h a) • Z (Fin.castLE h j) := by
    intro a; apply sum_castLE h; intro b hb
    rw [hτ (show id (Fin.castLE h a) < id b by simp only [id, Fin.lt_def, Fin.val_castLE]; omega), zero_smul]
  have hT : (τ.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro i j hij; simp only [submatrix_apply]; apply hτ
    simp only [id, Fin.lt_def, Fin.val_castLE] at hij ⊢; exact hij
  unfold Ga
  simp only [hs]
  have key := det_gram_tri (fun j => Z (Fin.castLE h j)) (τ.submatrix (Fin.castLE h) (Fin.castLE h)) hT
  simp only [submatrix_apply] at key
  rw [key, prod_Iic l, show star (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) * ∏ j, τ (Fin.castLE h j) (Fin.castLE h j) =
      ((Complex.normSq (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) : ℝ) : ℂ) from (Complex.normSq_eq_conj_mul_self).symm,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
