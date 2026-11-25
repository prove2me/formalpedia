-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.detD_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:29.607289+00:00
-- url     : https://prove2.me/submissions/eea68e51-33ea-4013-b1cc-a41cfbf3ad10

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[nhds 0] G) : detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]
end PositivityTheory.Rg.Sw.LVs
