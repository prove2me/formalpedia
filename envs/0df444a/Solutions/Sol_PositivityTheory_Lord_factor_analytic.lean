-- Prove2me | solution 1 for PositivityTheory.Lord.factor_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:48.503779+00:00
-- url     : https://prove2.me/submissions/e48cc40f-04e9-466f-8f94-bf6e43eb7707

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
import Theorems.Thm_PositivityTheory_Lord_factor_differentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution (N : ℕ) (hN : N ≠ 0) (c x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) x :=
  (PositivityTheory.Lord.factor_differentiable N hN c).analyticAt x
end PositivityTheory.Lord
