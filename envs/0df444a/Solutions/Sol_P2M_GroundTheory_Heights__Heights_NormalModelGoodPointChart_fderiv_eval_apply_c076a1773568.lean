-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:59.001063+00:00
-- url     : https://prove2.me/submissions/345d6ca8-ac42-4748-bb77-1bd610f8f8ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_hasFDerivAt_eval_7b0374bbcb50

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
open MvPolynomial Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (q : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    fderiv ℂ (fun z : σ → ℂ => eval z q) x v = ∑ s, eval x (pderiv s q) * v s := by
  rw [(hasFDerivAt_eval q x).fderiv]
  simp
end GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
