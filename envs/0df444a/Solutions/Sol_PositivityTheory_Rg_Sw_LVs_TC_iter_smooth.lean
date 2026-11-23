-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.iter_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:40.381008+00:00
-- url     : https://prove2.me/submissions/5e736770-9c0a-46ff-adc2-8b841ed6de4f

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) :
    ContDiffOn ℂ ∞ (iteratedFDeriv ℂ i F) Ω := by
  intro y hy
  have hle : (∞ : WithTop ℕ∞) + i ≤ ∞ := by
    exact_mod_cast (le_top : (⊤ : ℕ∞) + i ≤ ⊤)
  exact ((hF.contDiffAt (hΩ.mem_nhds hy)).iteratedFDeriv_right hle).contDiffWithinAt
end PositivityTheory.Rg.Sw.LVs.TC
