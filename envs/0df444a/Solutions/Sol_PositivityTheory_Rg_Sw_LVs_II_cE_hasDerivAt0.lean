-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.cE_hasDerivAt0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:43.583169+00:00
-- url     : https://prove2.me/submissions/2bcf0aa2-eb7d-4a05-b543-c4328b53942a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cE_entry

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
theorem _root_.solution (E : M2 n) : HasDerivAt (cE E) E 0 := by
  have h : HasDerivAt (fun s : ℝ => (cE E s : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
      (E : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => cE_entry E a b
  exact h
end PositivityTheory.Rg.Sw.LVs.II
