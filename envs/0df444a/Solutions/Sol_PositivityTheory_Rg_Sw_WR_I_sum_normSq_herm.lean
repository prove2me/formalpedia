-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.sum_normSq_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:23.208435+00:00
-- url     : https://prove2.me/submissions/8795329b-3efb-4ad8-9673-94cad442175c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_normSq_herm

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution (y : E n) :
    ∑ i, ∑ j, Complex.normSq (herm y i j) = ∑ a, ∑ b, y a b ^ 2 := by
  simp_rw [normSq_herm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => y j i ^ 2)]
  ring
end PositivityTheory.Rg.Sw.WR.I
