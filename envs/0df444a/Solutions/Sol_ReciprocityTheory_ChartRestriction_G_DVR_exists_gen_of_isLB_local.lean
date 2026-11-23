-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.489662+00:00
-- url     : https://prove2.me/submissions/7e1113d6-37b5-4f1a-b5c9-88ca171a541c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ M.U i := by
    have : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈
        (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
    rw [← hM.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop := eq_top_of_closedPoint_mem _ hi₀
  have hto : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i₀ := fun W => by
    rw [htop]
    exact le_top
  refine ⟨⟨fun i => res (le_inf le_rfl (hto _) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have hc := congrArg (res (le_inf le_rfl (hto _) : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀))
    (hM.cocycle i j i₀)
  simp only [map_mul, res_res'] at hc
  simp only [res_res']
  rw [← hc]
  congr 1
end ReciprocityTheory.ChartRestriction.G.DVR
