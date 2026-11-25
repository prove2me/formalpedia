-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.diagonal_curvature_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:08.492706+00:00
-- url     : https://prove2.me/submissions/dad0f645-999a-4f1a-80a9-d8d2a0dcd488

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sum_castLE__9f0ccf304156
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_two_correctedLineGramPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (a : Fin m) :
    (cf 2 (GnP hm D Y 1) + cf 2 (GnP hm D Y Complex.I)) a a = 2 * (Sa hm D Y a : ℂ) := by
  rw [coeffMatrix_two_correctedLineGramPoly, coeffMatrix_two_correctedLineGramPoly]
  have hc1 : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  have hcI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [hc1, hcI, one_mul, one_pow, one_smul, neg_mul, Complex.I_mul_I, neg_neg, Complex.I_sq,
    neg_sq, neg_smul, one_smul, sub_neg_eq_add]
  have e : ∀ (A P Q : Matrix (Fin m) (Fin m) ℂ), (A - P - Q) + (A + P + Q) = (2 : ℂ) • A := by
    intro A P Q; rw [two_smul]; abel
  rw [e, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Dc, Dm, Ym, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rw [sum_castLE' hm (fun k => star (Y k (Fin.castLE hm a)) * (D k : ℂ) * Y k (Fin.castLE hm a)),
    ← Finset.sum_sub_distrib, Sa]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < m
  · rw [if_pos hk, if_neg (by omega), sub_self]
    simp
  · rw [if_neg hk, if_pos (by omega), sub_zero, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.conj_mul', Complex.star_def]
    ring
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
