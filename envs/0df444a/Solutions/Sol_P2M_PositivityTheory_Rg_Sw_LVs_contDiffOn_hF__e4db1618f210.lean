-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_hF__e4db1618f210
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:43.39236+00:00
-- url     : https://prove2.me/submissions/37b20240-cf58-4533-9fa2-8418061cd5dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_wM
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_wM_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_minorOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_scalar_section_of_units
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dom_sub

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
theorem _root_.solution (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := by
  unfold hF
  refine (((contDiffOn_scalar_section_of_units p q).mono fun x hx => dom_sub x hx).mul
    (cdo_minorOn _ (cdo_wM _ fun x hx => hx.2.2.1))).mul (cdo_minorOn _ (cdo_wM_inv _ dom_sub))
end PositivityTheory.Rg.Sw.LVs
