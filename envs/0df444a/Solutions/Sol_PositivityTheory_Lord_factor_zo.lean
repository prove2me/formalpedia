-- Prove2me | solution 1 for PositivityTheory.Lord.factor_zo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:24.388043+00:00
-- url     : https://prove2.me/submissions/a6508ffe-bc92-417d-acf1-32e07233783a

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
import Theorems.Thm_PositivityTheory_Lord_factor_analytic
import Theorems.Thm_PositivityTheory_Lord_factor_ne_zero_int
import Theorems.Thm_PositivityTheory_Lord_PO_of_analytic
import Theorems.Thm_PositivityTheory_Lord_ZO_of_analytic


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
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    ZO (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) (j : ℂ) 0 :=
  PositivityTheory.Lord.ZO.of_analytic (PositivityTheory.Lord.factor_analytic N (by omega) c _)
    (PositivityTheory.Lord.factor_ne_zero_int N hN c hc j hj)
end PositivityTheory.Lord
