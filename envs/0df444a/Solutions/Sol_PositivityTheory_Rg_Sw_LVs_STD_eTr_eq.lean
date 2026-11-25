-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.eTr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:12.3838+00:00
-- url     : https://prove2.me/submissions/863e6c42-08cf-4b53-b2a7-e350d410ab3b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_ell_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (β : Matrix (Fin n) (Fin n) ℂ) (x : Vr n) : eTr β x = Complex.exp (ell β (herm x)) := by
  simp [eTr, ell_apply]
end PositivityTheory.Rg.Sw.LVs.STD
