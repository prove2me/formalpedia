-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linComb_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:57.600417+00:00
-- url     : https://prove2.me/submissions/e724d912-f239-4977-88a9-77f4d0f407eb

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
set_option maxHeartbeats 1000000
include hL
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (i j l : K → L.ι) :
    res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ j)
        ((LB.LinComb L φ ε).g i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ j ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g i l) := by
  simp only [LB.LinComb, map_prod, map_zpow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  congr 1
  erw [res_res', res_res', res_res']

  have hT : LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤
      (φ k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k)) := by
    intro y hy
    exact ⟨⟨LB.wchart_le L φ i k hy.1.1, LB.wchart_le L φ j k hy.1.2⟩, LB.wchart_le L φ l k hy.2⟩
  erw [res_pullU_eq (φ k) (inf_le_left : L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (i k) ⊓ L.U (j k)) _ hT,
    res_pullU_eq (φ k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (j k) ⊓ L.U (l k)) _ hT,
    res_pullU_eq (φ k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (i k) ⊓ L.U (l k)) _ hT]
  rw [← map_mul, ← map_mul, hL.cocycle]
end ReciprocityTheory.ChartRestriction.G.DVR
