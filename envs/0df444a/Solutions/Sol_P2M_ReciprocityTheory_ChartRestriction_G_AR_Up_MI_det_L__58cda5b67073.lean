-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_L__58cda5b67073
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:01.390545+00:00
-- url     : https://prove2.me/submissions/5f1536d8-4c1c-425f-aef7-9ed435ade1b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_keyU_injective
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__zero_ad1479de9b67
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_L__diag_bec3567a4726

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
theorem _root_.solution (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
