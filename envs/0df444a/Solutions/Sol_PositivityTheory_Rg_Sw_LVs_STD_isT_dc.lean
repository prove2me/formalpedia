-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.isT_dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:15.719111+00:00
-- url     : https://prove2.me/submissions/981502bb-cf07-4efe-9e11-dc15ab5bc009

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_contDiffOn_dc
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
theorem _root_.solution {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub
end PositivityTheory.Rg.Sw.LVs.STD
