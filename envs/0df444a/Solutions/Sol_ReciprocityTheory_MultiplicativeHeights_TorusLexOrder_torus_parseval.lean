-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torus_parseval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:08.379391+00:00
-- url     : https://prove2.me/submissions/a4fd3c38-5fb5-4283-bd42-61a708e80e4b

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_integrable_torus_term
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_coeff_integral
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_eval_torus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∫ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 ∂(torusProb ι) =
      ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 := by
  have key : ∀ θ, ((‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 : ℝ) : ℂ) =
      ∑ s ∈ f.support, conj (f.coeff s) *
        (MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)) := by
    intro θ
    have hc : conj (MvPolynomial.eval (torusPoint θ) f) =
        ∑ s ∈ f.support, conj (f.coeff s) * conj (torusMono θ s) := by
      conv_lhs => rw [eval_torus]
      simp [map_sum, map_mul]
    push_cast
    rw [show ((‖MvPolynomial.eval (torusPoint θ) f‖ : ℂ)) ^ 2 =
        MvPolynomial.eval (torusPoint θ) f * conj (MvPolynomial.eval (torusPoint θ) f) by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [integral_finset_sum _ (fun s _ => (integrable_torus_term f s).const_mul _)]
  simp_rw [integral_const_mul, torus_coeff_integral]
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
