-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurable_logEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:45.703535+00:00
-- url     : https://prove2.me/submissions/8d0e4e51-a88e-441a-ae56-eb7750c49a1e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_eval_torus

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
    Measurable fun θ : ι → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ := Real.measurable_log.comp (continuous_eval_torus f).norm.measurable
end ReciprocityTheory.MultiplicativeHeights
