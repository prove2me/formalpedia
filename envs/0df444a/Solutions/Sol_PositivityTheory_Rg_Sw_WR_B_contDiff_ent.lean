-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_ent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:10.496729+00:00
-- url     : https://prove2.me/submissions/77b1a89d-9a84-47b8-8413-e0549f7e87ab

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_uM_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_vM_entry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (e : Bool × Fin n × Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (ent (n := n) s e) := by
  unfold ent
  split_ifs
  · exact contDiff_vM_entry hs _ _
  · exact contDiff_uM_entry hs _ _
end PositivityTheory.Rg.Sw.WR.B
