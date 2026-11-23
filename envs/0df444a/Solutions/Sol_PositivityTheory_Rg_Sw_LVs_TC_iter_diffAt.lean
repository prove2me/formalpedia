-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iter_diffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:15.192362+00:00
-- url     : https://prove2.me/submissions/ed21aee9-02d5-48af-bdfe-fc9643ab8f05

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_smooth

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) {y : V} (hy : y ∈ Ω) :
    DifferentiableAt ℂ (iteratedFDeriv ℂ i F) y := by
  exact ((iter_smooth hΩ hF i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
end PositivityTheory.Rg.Sw.LVs.TC
