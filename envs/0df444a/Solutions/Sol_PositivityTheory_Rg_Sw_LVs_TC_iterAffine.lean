-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iterAffine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:15.178286+00:00
-- url     : https://prove2.me/submissions/b32cd25c-2a44-4e21-baa7-d9c5500a57ab

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc

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
theorem _root_.solution : IterAffine := by
  intro V W _ _ _ _ F Ω hΩ hF c hc L k
  have hT : Continuous (fun y : V => c + y) := continuous_const.add continuous_id
  have hΩ1 : IsOpen ((fun y : V => c + y) ⁻¹' Ω) := hΩ.preimage hT
  have hΩ2 : IsOpen (L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω)) := hΩ1.preimage L.continuous
  have hG : ContDiffOn ℂ ∞ (fun y : V => F (c + y)) ((fun y : V => c + y) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have hm2 : (0 : W) ∈ L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω) := by simpa using hc
  have hm1 : L 0 ∈ (fun y : V => c + y) ⁻¹' Ω := by simpa using hc
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hG hΩ1.uniqueDiffOn
    hΩ2.uniqueDiffOn hm1 hk
  rw [iteratedFDerivWithin_of_isOpen k hΩ2 hm2, iteratedFDerivWithin_of_isOpen k hΩ1 hm1,
    iteratedFDeriv_comp_add_left] at h1
  simp only [map_zero, add_zero] at h1
  exact h1
end PositivityTheory.Rg.Sw.LVs.TC
