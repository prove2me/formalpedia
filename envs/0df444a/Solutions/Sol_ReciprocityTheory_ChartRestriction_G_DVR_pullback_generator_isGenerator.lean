-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullback_generator_isGenerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:58.523779+00:00
-- url     : https://prove2.me/submissions/2fc27570-1794-4746-9c5f-dd3b10c57f16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res


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
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Z ⟶ Y) (i j : K → L.ι) :
    res (inf_le_left : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
        (LB.LinComb L (fun k => h ≫ φ k) ε).U i) ((LB.pullGen L φ ε t h).s i) =
      (LB.LinComb L (fun k => h ≫ φ k) ε).g i j *
        res (inf_le_right : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
          (LB.LinComb L (fun k => h ≫ φ k) ε).U j) ((LB.pullGen L φ ε t h).s j) := by
  have hW : (LB.LinComb L (fun k => h ≫ φ k) ε).U i ⊓ (LB.LinComb L (fun k => h ≫ φ k) ε).U j ≤
      h ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 k⟩
  have h1 := congrArg (fun z : Γ(Y, ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j))ˣ =>
    res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) z)) (ht i j)
  simp only [map_mul, pullU_res, res_res'] at h1
  have e0 : (LB.LinComb L φ ε).g i j = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)) :
        ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
      (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k) := rfl
  have e1 : (LB.LinComb L (fun k => h ≫ φ k) ε).g i j = ∏ k, (res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)
      (res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)) :
        ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
      (pullU (φ k) _ (L.g (i k) (j k)))))) ^ (ε k) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    erw [pullU_res, res_res']
    try rfl
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K → Γ(Y, ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j))ˣ, (LB.LinComb L φ ε).g i j = ∏ k, a k ^ ε k ∧
      (LB.LinComb L (fun k => h ≫ φ k) ε).g i j = ∏ k, (res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) (a k))) ^ ε k :=
    ⟨_, e0, e1⟩
  have hg : (LB.LinComb L (fun k => h ≫ φ k) ε).g i j =
      res hW (pullU h ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) ((LB.LinComb L φ ε).g i j)) := by
    rw [ha1, ha0]
    first
      | (rw [map_prod, map_prod]; exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow])
      | simp only [map_prod, map_zpow]
  rw [hg]
  erw [res_res', res_res']
  exact h1
end ReciprocityTheory.ChartRestriction.G.DVR
