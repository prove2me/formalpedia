-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwPoly_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:47.585982+00:00
-- url     : https://prove2.me/submissions/6f8bf1f3-7f31-471d-b628-8eb6070ef3c4

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyB
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPoly
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_smul_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_ext_poly
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_det_id_line
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_det_line
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_line_poly
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_poly_eq_of_eval_eq_off


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hH : LemmaHStatement) (hE : ∀ n, ReciprocityTheory.L2DbarEstimates.EXTStatement n)
    (hO : OnePolyGrowthStatement) : BWPolyStatement := by
  intro p a P hP hT
  obtain ⟨F, hF⟩ := bwp_ext_poly (σ := Fin p × Fin p) (∑ i, a i) (fun z => P (bwpMat z))
    (fun z => (bwpMat z).det) (bwpId p) (fun z => bwp_finite_det_id_line z)
    (fun z v hz => bwp_finite_det_line z v hz) (fun z v hB => bwp_line_poly hH hO a P hP hT z v hB)
  have hF' : ∀ z, (bwpMat z).det ≠ 0 → P (bwpMat z) = MvPolynomial.eval z F := fun z hz => hF z hz
  refine ⟨MvPolynomial.homogeneousComponent (∑ i, a i) F,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun x hx => ?_⟩
  set z : Fin p × Fin p → ℂ := fun ij => x ij.1 ij.2 with hz
  have hxz : bwpMat z = x := by
    ext i j
    rfl
  have hPz : P x = MvPolynomial.eval z F := by
    rw [← hxz]
    exact hF' z (by rw [hxz]; exact hx)
  rw [hPz]
  have hscale : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (t • z) F = t ^ (∑ i, a i) * MvPolynomial.eval z F := by
    intro t ht
    have hb : bwpMat (t • z) = x * (t • (1 : Matrix (Fin p) (Fin p) ℂ)) := by
      ext i j
      simp [bwpMat, hz, Matrix.mul_smul]
    have hbdet : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).det ≠ 0 := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ ht
    have hbtri : (t • (1 : Matrix (Fin p) (Fin p) ℂ)).BlockTriangular id := by
      intro i j h
      have hij : i ≠ j := fun hij => by subst hij; exact lt_irrefl _ h
      rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
    have hdet : (bwpMat (t • z)).det ≠ 0 := by
      rw [hb, Matrix.det_mul]
      exact mul_ne_zero hx hbdet
    rw [← hF' _ hdet, hb, hT x _ hx hbdet hbtri, hPz]
    congr 1
    simp [triChar, Finset.prod_pow_eq_pow_sum]
  have hsum : ∀ t : ℂ, MvPolynomial.eval (t • z) F = ∑ j ∈ Finset.range (F.totalDegree + 1),
      t ^ j * MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F) := by
    intro t
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent F]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => bwp_eval_smul_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous j F) t z)
  have hΦ : (∑ j ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (MvPolynomial.eval z (MvPolynomial.homogeneousComponent j F)) * Polynomial.X ^ j) =
      Polynomial.C (MvPolynomial.eval z F) * Polynomial.X ^ (∑ i, a i) := by
    refine bwp_poly_eq_of_eval_eq_off _ _ {0} (Set.finite_singleton 0) (fun t ht => ?_)
    have ht0 : t ≠ 0 := ht
    rw [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, mul_comm, ← hscale t ht0, hsum t]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hc := congrArg (fun q => Polynomial.coeff q (∑ i, a i)) hΦ
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  rw [Finset.sum_ite_eq] at hc
  split_ifs at hc with hk
  · exact hc.symm
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hk), map_zero]
    exact hc.symm
end ReciprocityTheory.MultiplicativeHeights
