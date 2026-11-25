-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.tsupport_dList_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:39.429981+00:00
-- url     : https://prove2.me/submissions/d21a6c8f-ece7-4bab-b9b0-5124db786f55

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_support_dc_subset

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
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (solution φ l))
      (isClosed_tsupport φ))
end PositivityTheory.Rg.Sw.LVs.STD
