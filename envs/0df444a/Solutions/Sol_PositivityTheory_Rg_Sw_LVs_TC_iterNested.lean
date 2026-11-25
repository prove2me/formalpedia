-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iterNested
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:10.949221+00:00
-- url     : https://prove2.me/submissions/2d6693b4-2e48-4a90-9bc9-412b1c4e5b2f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iterAffine
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_eval_smooth
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_mixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : IterNested := by
  intro V W1 W2 _ _ _ _ _ _ F Ω hΩ hF c hc L1 L2 a b u w
  have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x (fun i => L2 (w i))) Ω :=
    eval_smooth hΩ hF b _
  have hU : ∀ᶠ t1 in 𝓝 (0 : W1), c + L1 t1 ∈ Ω := by
    have hcont : Continuous (fun t1 : W1 => c + L1 t1) := continuous_const.add L1.continuous
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hc
  have he : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    filter_upwards [hU] with t1 ht1
    rw [iterAffine V W2 F Ω hΩ hF (c + L1 t1) ht1 L2 b]
    rfl
  have he' : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝[univ] 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    rw [nhdsWithin_univ]
    exact he
  have hE := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℂ) he' he.eq_of_nhds a
  simp only [iteratedFDerivWithin_univ] at hE
  rw [hE, iterAffine V W1 _ Ω hΩ hg c hc L1 a]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact iter_mixed hΩ hF b _ a hc _
end PositivityTheory.Rg.Sw.LVs.TC
