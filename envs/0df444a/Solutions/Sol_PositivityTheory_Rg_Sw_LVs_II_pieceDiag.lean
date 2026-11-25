-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.pieceDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:33.904784+00:00
-- url     : https://prove2.me/submissions/40989308-5d92-4267-859e-a8923377496d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_deriv_piece
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_inG_fromBlocks_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_det_one_add_smul_single_same
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_one_add_smul_single_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
namespace PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem one_add_smul_single_conjTranspose_mul_eq_one (a b : ℂ) (h : (1 + star a) * (1 + b) = 1) (i : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + a • Matrix.single i i 1)ᴴ * (1 + b • Matrix.single i i 1) = 1 := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_single, star_one, one_add_smul_single_mul]
  have h0 : star a + b + star a * b = 0 := by linear_combination h
  rw [h0, zero_smul, add_zero]
end PositivityTheory.Rg.Sw.LVs.II
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i : Fin n) :
    fderiv ℂ Θ x (Pij c i i * x) = lam (Pij c i i) * Θ x := by
  have e : ∀ w : ℂ, (1 : ℂ) + (w - 1) = w := fun w => by ring
  have hu : HasDerivAt (fun t : ℝ => Complex.exp (↑t * c) - 1) c 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const c).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hv : HasDerivAt (fun t : ℝ => Complex.exp (-↑t * conj c) - 1) (-(conj c)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).neg.mul_const (conj c)).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hγ : HasDerivAt (fun t : ℝ => (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)))
      (Pij c i i) 0 := by
    have h := ((hu.smul_const (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n)).add
      (hv.smul_const (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).const_add (1 : M2 n)
    refine h.congr_deriv ?_
    rw [Pij, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  have hform : ∀ t : ℝ, (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)) =
      fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
        (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) := by
    intro t
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add, Matrix.fromBlocks_add]
    simp
  have hG : ∀ t : ℝ, InG (fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
      (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) : M2 n) := by
    intro t
    apply inG_fromBlocks_diag
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (↑t * c) + -↑t * conj c : ℂ) = 0 by rw [map_mul, Complex.conj_ofReal]; ring,
        Complex.exp_zero]
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (-↑t * conj c) + ↑t * c : ℂ) = 0 by
          rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]; ring,
        Complex.exp_zero]
  have hf := (((hasDerivAt_id' (0 : ℝ)).const_mul (2 * (n : ℝ) * c.re)).exp).ofReal_comp
  have key := deriv_piece Θ x hd _ _ hγ (by simp) _ _ hf
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) +
          ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
            (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).toBlocks₂₁ = 0 := by
        rw [hform]
        simp
      rw [hl _ x (by rw [hform]; exact hG t) h21 hx, hform, Matrix.toBlocks_fromBlocks₂₂,
        det_one_add_smul_single_same, e, Complex.norm_exp]
      congr 2
      rw [← Real.rpow_intCast, ← Real.exp_mul]
      congr 1
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im,
        Complex.conj_re, Complex.conj_im]
      push_cast
      ring)
  rw [key]
  congr 1
  simp [lam, Pij, Matrix.trace_smul]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.LVs.II
