-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.isGen_pullAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:31.51284+00:00
-- url     : https://prove2.me/submissions/217da4da-4766-4efe-8aca-18445592ec04

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullU_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pull_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullAlong
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.LBxP
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')
section Germ
variable {X X' Y Y' Z Z' : Scheme.{0}}
variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
private lemma gU_pull_g_lemma_2 (F : X' ⟶ X) (h : Y' ⟶ Y) (φk : Y ⟶ X) (ψk : Y' ⟶ X')
    (hk : ψk ≫ F = h ≫ φk) (i j : PUnit → L.ι) (y : Y')
    (hy : y ∈ ψk ⁻¹ᵁ ((L.pull F).U i ⊓ (L.pull F).U j))
    (hy' : h.base y ∈ φk ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩))) :
    gU y hy (pullU ψk _ ((L.pull F).g i j)) =
      Units.map (h.stalkMap y).hom (gU (h.base y) hy' (pullU φk _ (L.g (i ⟨⟩) (j ⟨⟩)))) := by
  have h1 : y ∈ (ψk ≫ F) ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) := by
    rw [hk]; exact hy'
  rw [gU_pull_g L F ψk i j y hy h1,
    gU_pullU_congr hk (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) (L.g (i ⟨⟩) (j ⟨⟩)) y h1 hy',
    ← gU_pullU_comp h φk (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩)) (L.g (i ⟨⟩) (j ⟨⟩)) y hy' hy']
  exact gU_pullU h _ y _ _
end Germ
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBxP
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')
variable {X X' Y Y' Z Z' : Scheme.{0}}
variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Out.LBxP
theorem _root_.solution (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : (GeneratorPullback.pullAlong L F h φ ε ψ hψ t).IsGen := by
  unfold LB.Gen.IsGen at ht ⊢
  intro i j
  apply unit_ext
  intro y hy
  have hb : h.base y ∈ (LB.LinComb L φ ε).U (fun k => i k ⟨⟩) ⊓
      (LB.LinComb L φ ε).U (fun k => j k ⟨⟩) :=
    ⟨GeneratorPullback.pullAlong_le L F h φ ψ hψ i hy.1, GeneratorPullback.pullAlong_le L F h φ ψ hψ j hy.2⟩
  have kk := (gU_res _ (h.base y) hb _).symm.trans
    ((congrArg (gU (h.base y) hb) (ht (fun k => i k ⟨⟩) (fun k => j k ⟨⟩))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gU_lcg L φ ε _ _ (h.base y) hb)
        (gU_res _ (h.base y) hb _))))
  refine ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t i y _)).trans ?_
  refine Eq.trans ?_ ((map_mul (gU y hy) _ _).trans (congrArg₂ (· * ·) (gU_lcg (L.pull F) ψ ε i j y hy)
    ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t j y _)))).symm
  refine (congrArg (Units.map (h.stalkMap y).hom.toMonoidHom) kk).trans ?_
  rw [map_mul, map_prod]
  refine congrArg₂ (fun a b => a * b) (Finset.prod_congr rfl fun k _ => ?_) rfl
  rw [map_zpow]
  exact congrArg (· ^ ε k) (gU_pull_g_lemma_2 L F h (φ k) (ψ k) (hψ k) (i k) (j k) y _ _).symm
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
