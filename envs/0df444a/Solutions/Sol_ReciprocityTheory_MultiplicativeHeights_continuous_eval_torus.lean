-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.continuous_eval_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:59.60526+00:00
-- url     : https://prove2.me/submissions/fcc083fc-088b-4b48-afa3-416a3cf2254f

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB

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
theorem _root_.solution (f : MvPolynomial ι ℂ) :
    Continuous fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f := by
  exact (MvPolynomial.continuous_eval f).comp (continuous_pi fun j => by unfold torusPoint; fun_prop)
end ReciprocityTheory.MultiplicativeHeights
