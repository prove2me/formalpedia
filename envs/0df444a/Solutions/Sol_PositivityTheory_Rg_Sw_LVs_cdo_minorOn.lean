-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_minorOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:45.505411+00:00
-- url     : https://prove2.me/submissions/a138fb80-d56f-41d1-80e0-3ed6a4043f26

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_det

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
theorem _root_.solution {s : Set E} (t : Finset (Fin n)) {M : E → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => minorOn t (M x)) s :=
  cdo_det fun i j => hM _ _
end PositivityTheory.Rg.Sw.LVs
