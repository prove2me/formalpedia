-- Prove2me | solution 1 for PI.EF.order_ne_top_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:46.502165+00:00
-- url     : https://prove2.me/submissions/4cd183a3-c974-4604-acc5-3a20457dd339

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set
namespace PI.EF
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (y : ℂ) : analyticOrderAt f y ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ y) htop
  exact hx (h0 (Set.mem_univ x))
end PI.EF
