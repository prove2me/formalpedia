-- Prove2me | solution 1 for PositivityTheory.RgJS.RemovableSingularityAlt.analytic_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:55.085149+00:00
-- url     : https://prove2.me/submissions/84abd3ce-93d9-40f5-bde0-5e0632f8472c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds
import Theorems.Thm_PositivityTheory_RgJS_RemovableSingularityAlt_analyticAt_dslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.RemovableSingularityAlt
namespace PositivityTheory.RgJS.RemovableSingularityAlt
theorem _root_.solution {G : ℂ → ℂ} (hG : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) :
    ∀ j, ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ (D G j) σ
  | 0 => hG
  | j + 1 => fun σ hσ => by
      have h1 := solution hG j 1 one_pos
      simp only [Complex.ofReal_one] at h1
      exact analyticAt_dslope h1 (solution hG j σ hσ)
end PositivityTheory.RgJS.RemovableSingularityAlt
