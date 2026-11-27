-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.corr_pullAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:54.899244+00:00
-- url     : https://prove2.me/submissions/dd91114b-4944-4f5b-a19a-d41b650196dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
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
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (ψ : K → (Y' ⟶ X')) (ψ' : K' → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (hψ' : ∀ k, ψ' k ≫ F = h ≫ φ' k)
    (hinj : ∀ a b : K ⊕ K', Sum.elim ψ ψ' a ≫ F = Sum.elim ψ ψ' b ≫ F →
      Sum.elim ψ ψ' a = Sum.elim ψ ψ' b)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') :
    LB.Gen.Corr (L.pull F) ψ ε ψ' ε' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t)
      (GeneratorPullback.pullAlong L F h φ' ε' ψ' hψ' t') := by
  unfold LB.Gen.Corr at hc ⊢
  intro j j' hj hj' hjj
  have c1 : LB.Coh L φ (fun k => j k ⟨⟩) := fun k₁ k₂ e =>
    congrFun (hj k₁ k₂ (hinj (Sum.inl k₁) (Sum.inl k₂) (by
      show ψ k₁ ≫ F = ψ k₂ ≫ F
      rw [hψ, hψ, e]))) ⟨⟩
  have c2 : LB.Coh L φ' (fun k => j' k ⟨⟩) := fun k₁ k₂ e =>
    congrFun (hj' k₁ k₂ (hinj (Sum.inr k₁) (Sum.inr k₂) (by
      show ψ' k₁ ≫ F = ψ' k₂ ≫ F
      rw [hψ', hψ', e]))) ⟨⟩
  have c3 : ∀ k k', φ k = φ' k' → j k ⟨⟩ = j' k' ⟨⟩ := fun k k' e =>
    congrFun (hjj k k' (hinj (Sum.inl k) (Sum.inr k') (by
      show ψ k ≫ F = ψ' k' ≫ F
      rw [hψ, hψ', e]))) ⟨⟩
  have key := hc (fun k => j k ⟨⟩) (fun k => j' k ⟨⟩) c1 c2 c3
  apply unit_ext
  intro y hy
  have hb : h.base y ∈ LB.wchart L φ (fun k => j k ⟨⟩) ⊓ LB.wchart L φ' (fun k => j' k ⟨⟩) :=
    ⟨GeneratorPullback.pullAlong_le L F h φ ψ hψ j hy.1, GeneratorPullback.pullAlong_le L F h φ' ψ' hψ' j' hy.2⟩
  have kk := (gU_res _ (h.base y) hb _).symm.trans
    ((congrArg (gU (h.base y) hb) key).trans (gU_res _ (h.base y) hb _))
  exact ((gU_res _ y hy _).trans (gU_pullAlong L F h φ ε ψ hψ t j y _)).trans
    ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom) kk).trans
      ((gU_res _ y hy _).trans (gU_pullAlong L F h φ' ε' ψ' hψ' t' j' y _)).symm)
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
