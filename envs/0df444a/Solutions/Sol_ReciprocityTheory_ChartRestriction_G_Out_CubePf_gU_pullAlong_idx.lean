-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.gU_pullAlong_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:34.186985+00:00
-- url     : https://prove2.me/submissions/b93609c3-bed4-4943-b483-b5e47814d675

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullU_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_gU_isGen


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr base_eq)
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {X X' Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (jj : K → (L.pull F).ι) (y : Y') (hy : y ∈ LB.wchart (L.pull F) ψ jj)
    (idx : (Y' ⟶ X) → L.ι)
    (mk : ∀ k, y ∈ (ψ k ≫ F) ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F))))
    (mem0 : h.base y ∈ LB.wchart L φ (fun k => idx (ψ k ≫ F))) :
    gU y hy ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      (∏ k, (gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F))))) ^ (ε k)) *
        Units.map (h.stalkMap y).hom (gU (h.base y) mem0 (t.s (fun k => idx (ψ k ≫ F)))) := by
  have m1 := GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hy
  have step : ∀ k (hk : h.base y ∈ φ k ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F)))),
      Units.map (h.stalkMap y).hom (gU (h.base y) hk
        (pullU (φ k) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F))))) =
      gU y (mk k) (pullU (ψ k ≫ F) _ (L.g (jj k ⟨⟩) (idx (ψ k ≫ F)))) := by
    intro k hk
    have hk' : y ∈ h ⁻¹ᵁ (φ k ⁻¹ᵁ (L.U (jj k ⟨⟩) ⊓ L.U (idx (ψ k ≫ F)))) := hk
    exact (gU_pullU h _ y hk' _).symm.trans ((LBxP.gU_pullU_comp h (φ k) _ _ y hk'
      (show y ∈ (h ≫ φ k) ⁻¹ᵁ _ from hk)).trans (gU_pullU_congr (hψ k).symm _ _ y _ _))
  refine (LBxP.gU_pullAlong L F h φ ε ψ hψ t jj y hy).trans ?_
  rw [Semi.Transport.gU_isGen ht (h.base y) m1 mem0, map_mul]
  erw [LBxP.gU_lcg L φ ε (fun k => jj k ⟨⟩) (fun k => idx (ψ k ≫ F)) (h.base y) ⟨m1, mem0⟩]
  rw [map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (step k _)
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
