-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logLogCut_eventually_step_6e2f648e0cf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:10.07655+00:00
-- url     : https://prove2.me/submissions/10348bf5-baff-42be-848f-18d4362be74e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) {y : Fin m → ℂ}
    (h0 : 0 < ‖eval y Q‖ ^ 2) (h1 : ‖eval y Q‖ ^ 2 < 1) :
    logLogCut Q k =ᶠ[𝓝 y] fun z => cutStep (Real.log (-logAbsSq Q z) / ((k : ℝ) + 1)) := by
  filter_upwards [(continuousAt_normSq_eval Q y).preimage_mem_nhds (Ioo_mem_nhds h0 h1)] with z hz
  have hz : ‖eval z Q‖ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := hz
  unfold logLogCut
  rw [if_neg hz.1.ne', if_neg (not_le.2 hz.2)]
end GroundTheory.Heights₂.Heights
