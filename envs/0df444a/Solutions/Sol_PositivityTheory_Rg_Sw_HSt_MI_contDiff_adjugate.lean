-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.contDiff_adjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:38.019969+00:00
-- url     : https://prove2.me/submissions/e944f53f-8769-4888-b4fd-7dee3e464538

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_of_entries
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.MI
theorem _root_.solution : ContDiff ℝ ∞ (fun x : M2 n => x.adjugate) := by
  refine contDiff_of_entries fun a b => ?_
  have : (fun x : M2 n => x.adjugate a b) = fun x => (x.updateRow b (Pi.single a 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [this]
  refine contDiff_det.comp (contDiff_of_entries fun c d => ?_)
  by_cases h : c = b
  · subst h; simpa [Matrix.updateRow_self] using (contDiff_const : ContDiff ℝ ∞ fun _ : M2 n => (Pi.single a (1 : ℂ) : _ → ℂ) d)
  · simpa [Matrix.updateRow_ne h] using contDiff_entry (n := n) c d
end PositivityTheory.Rg.Sw.HSt.MI
