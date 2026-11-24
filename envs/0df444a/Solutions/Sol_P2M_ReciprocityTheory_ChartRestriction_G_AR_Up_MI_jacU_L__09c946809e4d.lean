-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jacU_L__09c946809e4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:59.5558+00:00
-- url     : https://prove2.me/submissions/b07dcffb-8ef0-46e7-a094-1385ba011f56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_L__diag_9e328cd12959

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (y : UpI ι r → ℂ) :
    jacU (Lβ β y) = jacβ β * jacU y := by
  unfold jacU jacβ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact Lβ_diag β hβ y i.1 i.2.2
  · simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
