-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.cE_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:16.572381+00:00
-- url     : https://prove2.me/submissions/2839be92-4203-4f8d-9f35-f64b6ea157de

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cE_hasDerivAt0
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cE_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (E : M2 n) (s : ℝ) : HasDerivAt (cE E) (cE E s * E) s := by
  have h0 : HasDerivAt (fun t : ℝ => cE E (t - s)) E s := by
    have h : HasDerivAt (cE E) E (s - s) := by simpa using cE_hasDerivAt0 E
    exact HasDerivAt.comp_sub_const s s h
  have h1 : HasDerivAt (fun t : ℝ => cE E s * cE E (t - s)) (cE E s * E) s :=
    (mulL (cE E s)).hasFDerivAt.comp_hasDerivAt s h0
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [← cE_add]
  congr 1
  ring
end PositivityTheory.Rg.Sw.LVs.II
