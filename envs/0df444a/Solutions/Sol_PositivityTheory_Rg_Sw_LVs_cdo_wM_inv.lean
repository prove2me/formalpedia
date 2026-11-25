-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_wM_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:31.959665+00:00
-- url     : https://prove2.me/submissions/13a19ff8-8340-4945-8fdf-1c096a29c2fc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_wM
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_wM

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
theorem _root_.solution (s : Set (M2 n)) (hs : ∀ x ∈ s, (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (wM x)⁻¹ i j) s :=
  cdo_inv (cdo_wM s fun x hx => (hs x hx).2) fun x hx => by
    rw [det_wM x (hs x hx).2]; exact mul_ne_zero (inv_ne_zero (hs x hx).2) (hs x hx).1
end PositivityTheory.Rg.Sw.LVs
