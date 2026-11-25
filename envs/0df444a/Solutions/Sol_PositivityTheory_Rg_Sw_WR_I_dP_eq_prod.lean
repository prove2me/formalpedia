-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.dP_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:39.446996+00:00
-- url     : https://prove2.me/submissions/5a48cd3f-2541-4d81-83b6-71e389d45151

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_sum_normSq_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution (y : E n) :
    dP y = ∏ i, (1 + (herm_isHermitian y).eigenvalues i ^ 2) ∧
      ∑ a, ∑ b, y a b ^ 2 = ∑ i, (herm_isHermitian y).eigenvalues i ^ 2 := by
  set hA := herm_isHermitian y
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self _
  have hsU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : herm y = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hsq : 1 + herm y * herm y = U * (1 + D * D) * star U := by
    rw [hspec]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hsU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  have hDD : 1 + D * D = diagonal fun i => ((1 + hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    funext i
    simp [pow_two]
  have hdetU : U.det * (star U).det = 1 := by rw [← det_mul, hsU, det_one]
  constructor
  · unfold dP
    rw [hsq, det_mul, det_mul, hDD, det_diagonal]
    rw [mul_comm U.det, mul_assoc, hdetU, mul_one, ← Complex.ofReal_prod, Complex.ofReal_re]
  · have hsq2 : herm y * herm y = U * (D * D) * star U := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
    have htr : (herm y * herm y).trace = ∑ i, ((hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
      rw [hsq2, trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul, hD, diagonal_mul_diagonal, trace_diagonal]
      simp [pow_two]
    have hre : (herm y * herm y).trace.re = ∑ i, ∑ j, Complex.normSq (herm y i j) := by
      rw [trace]
      simp only [diag_apply, mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hji : herm y j i = star (herm y i j) := by
        have := congrFun (congrFun hA.eq j) i
        rw [conjTranspose_apply] at this
        exact this.symm
      rw [hji, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    rw [← sum_normSq_herm, ← hre, htr, Complex.re_sum]
    simp only [Complex.ofReal_re]
end PositivityTheory.Rg.Sw.WR.I
