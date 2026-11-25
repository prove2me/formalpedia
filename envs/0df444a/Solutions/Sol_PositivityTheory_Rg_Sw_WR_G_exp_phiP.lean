-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.exp_phiP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:25.433279+00:00
-- url     : https://prove2.me/submissions/a7c5e6bc-dd08-49a8-b063-aa53d2319a0c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gramX_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_phiP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) = Complex.exp (evX (phiP ε c t b) x) := by
  rw [gs, ← Complex.exp_add, evX_phiP]
  congr 1
  have h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    have hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.star_def, hz]; push_cast; ring
  have h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j := by
    simp only [trace, diag, mul_apply, gramX_apply, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j =
      (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j) := by
    intro a k
    simp only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_eq, mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [h1, h2]
  simp only [h3, Finset.sum_sub_distrib, Finset.mul_sum]
  ring
end PositivityTheory.Rg.Sw.WR.G
