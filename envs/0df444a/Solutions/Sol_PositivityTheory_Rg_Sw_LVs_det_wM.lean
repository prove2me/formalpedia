-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_wM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:39.303565+00:00
-- url     : https://prove2.me/submissions/848fad54-3ae3-46b2-a338-88b057b13650

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (x : M2 n) (h2 : (u2 x).det ≠ 0) : (wM x).det = ((u2 x).det)⁻¹ * (u1 x).det := by
  rw [wM, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
end PositivityTheory.Rg.Sw.LVs
