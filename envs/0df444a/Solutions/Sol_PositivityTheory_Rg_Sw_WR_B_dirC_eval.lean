-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:57.021417+00:00
-- url     : https://prove2.me/submissions/10d9792e-ca46-4609-86b4-cb0aadc5be47

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_const
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_add
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → E n → ℂ) (hφ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i))
    (w : Fin n → Fin n → ℂ) (y : E n) (R : MvPolynomial ι ℂ) :
    dirC (fun y => MvPolynomial.eval (fun i => φ i y) R) w y =
      ∑ i, MvPolynomial.eval (fun i => φ i y) (MvPolynomial.pderiv i R) * dirC (φ i) w y := by
  have hd : ∀ (P : MvPolynomial ι ℂ), DifferentiableAt ℝ (fun y => MvPolynomial.eval (fun i => φ i y) P) y :=
    fun P => ((contDiff_eval φ hφ P).differentiable (by simp)).differentiableAt
  have hdi : ∀ i, DifferentiableAt ℝ (φ i) y := fun i => ((hφ i).differentiable (by simp)).differentiableAt
  induction R using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
           exact dirC_const a w y
  | add p q hp hq =>
    simp only [map_add]
    rw [dirC_add (hd p) (hd q), hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  | mul_X p j hp =>
    have hs : ∀ x, (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x (p * MvPolynomial.X j)) =
        (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x p) * φ j y +
          (if j = x then (MvPolynomial.eval fun i => φ i y) p else 0) := by
      intro x
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
      by_cases hx : j = x
      · subst hx; simp; ring
      · simp [hx]; ring
    simp only [map_mul, MvPolynomial.eval_X]
    rw [dirC_mul (hd p) (hdi j), hp]
    simp only [hs, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
end PositivityTheory.Rg.Sw.WR.B
