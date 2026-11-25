-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linComb_g_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:00.200545+00:00
-- url     : https://prove2.me/submissions/0af4e4c7-1b08-4397-9b16-a61211fe72cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_pullU_eq

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
include hL
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j j) = 1 := by
  simp only [LB.LinComb, map_prod, map_zpow]
  refine Finset.prod_eq_one fun k _ => ?_
  erw [res_res', res_pullU_eq (φ k) (le_inf le_rfl le_rfl) _ (LB.wchart_le L φ j k), hL.g_self]
  rw [map_one, map_one, one_zpow]
end ReciprocityTheory.ChartRestriction.G.DVR
