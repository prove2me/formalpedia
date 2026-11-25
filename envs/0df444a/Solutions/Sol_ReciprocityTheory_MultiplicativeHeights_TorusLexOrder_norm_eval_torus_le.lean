-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.norm_eval_torus_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:23.216361+00:00
-- url     : https://prove2.me/submissions/81b07cb6-5b65-4b09-9f5d-d2baf00d5119

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_torusMono
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
theorem _root_.solution {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [eval_torus]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [norm_mul, norm_torusMono, mul_one]
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
