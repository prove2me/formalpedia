-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.sum_vkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:17.885994+00:00
-- url     : https://prove2.me/submissions/366f237d-2258-4e21-a756-28cad5089fc0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_sum_single

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution (β : E n) (k l : Fin n) : ∑ a, ∑ b, (β a b : ℂ) * vkl k l a b = herm β k l := by
  simp only [vkl, mul_add, Finset.sum_add_distrib, sum_single]
  rw [herm_apply']
  push_cast
  ring
end PositivityTheory.Rg.Sw.WR.Ib
