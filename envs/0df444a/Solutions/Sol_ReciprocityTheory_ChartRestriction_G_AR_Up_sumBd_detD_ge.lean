-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_detD_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:26.559477+00:00
-- url     : https://prove2.me/submissions/c3d1e1c2-1442-401c-8fbd-0afca4a35906

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_trace_ctm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_det_one_add_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_normSq_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    1 + sumBdFsq M.toBlocks₁₂ ≤ Complex.normSq (det M.toBlocks₂₂) := by
  rw [← sumBd_normSq_det, (sumBdIsUpq_blocks h).2.1, ← sumBd_trace_ctm]
  exact sumBd_det_one_add_ge (posSemidef_conjTranspose_mul_self _)
end ReciprocityTheory.ChartRestriction.G.AR.Up
