-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.norm_eval_torus_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:49.868838+00:00
-- url     : https://prove2.me/submissions/3b8cc6c8-617b-4d02-9373-da374d611c9c

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_torusPoint

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
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  rw [norm_mul, norm_prod]
  simp [norm_pow, norm_torusPoint]
end ReciprocityTheory.MultiplicativeHeights
