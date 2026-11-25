-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_eq_zero_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:30.901833+00:00
-- url     : https://prove2.me/submissions/2a7d309e-4909-4aae-9a44-c9b4fdb89ae1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_def
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_totalDegree_pderiv_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_pderiv_eq_zero_of_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (c : σ → σ → k) (Q : MvPolynomial σ k) (h : Q.totalDegree ≤ 1) :
    secondOrder k c Q = 0 := by
  rw [so_def]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_
  have h1 := totalDegree_pderiv_le l' Q
  rw [pderiv_eq_zero_of_deg l (pderiv l' Q) (by omega), mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
