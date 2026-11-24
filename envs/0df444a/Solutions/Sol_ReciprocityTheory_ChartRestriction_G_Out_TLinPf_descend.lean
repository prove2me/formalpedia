-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:01.007607+00:00
-- url     : https://prove2.me/submissions/33e2d8ba-8961-4d70-b849-4fdd0cc23b96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_fnOf_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_fnOf_mOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_mOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_kp

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution (ρ : Γ((thickObj R I e G).left, ⊤))
    (h : (WeightPf.act g).left.appTop.hom ρ =
      (snd (WeightPf.Te D I e) (thickObj R I e G)).left.appTop.hom ρ) :
    ∃ v : Γ((thickObj R I e D.P.A).left, ⊤), g.q.left.appTop.hom v = ρ := by
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  let 𝒰 := (thickObj R I e D.P.A).left.affineCover
  have hloc : ∀ i, ∃ u : 𝒰.X i ⟶ A1,
      pullback.snd g.q.left (𝒰.f i) ≫ u = pullback.fst g.q.left (𝒰.f i) ≫ mOf ρ := by
    intro i
    have : IsAffine (pullback g.q.left (𝒰.f i)) := isAffine_of_isAffineHom (pullback.snd g.q.left (𝒰.f i))
    have : IsRegularEpi (pullback.snd g.q.left (𝒰.f i)) :=
      isRegularEpi_of_flat_of_surjective_of_isAffine _
    refine IsRegularEpi.exists_of_isKernelPair _ (IsKernelPair.of_hasPullback _) _ ?_
    rw [← Category.assoc, ← Category.assoc, comp_mOf, comp_mOf]
    congr 1
    refine kp g ρ h _ _ ?_
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition_assoc]
  choose u hu using hloc
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    let c := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have : Epi (pullback.snd g.q.left c) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd g.q.left c)]
    have li : pullback.snd g.q.left c ≫ pullback.fst (𝒰.f i) (𝒰.f j) =
        pullback.lift (pullback.fst g.q.left c) (pullback.snd g.q.left c ≫ pullback.fst _ _)
          (by rw [pullback.condition, Category.assoc]) ≫ pullback.snd g.q.left (𝒰.f i) := by
      rw [pullback.lift_snd]
    have lj : pullback.snd g.q.left c ≫ pullback.snd (𝒰.f i) (𝒰.f j) =
        pullback.lift (pullback.fst g.q.left c) (pullback.snd g.q.left c ≫ pullback.snd _ _)
          (by rw [pullback.condition]; show _ ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = _
              rw [pullback.condition, Category.assoc])
          ≫ pullback.snd g.q.left (𝒰.f j) := by
      rw [pullback.lift_snd]
    rw [← Category.assoc, li, Category.assoc, hu, pullback.lift_fst_assoc, ← Category.assoc, lj,
      Category.assoc, hu, pullback.lift_fst_assoc]
  have hU : g.q.left ≫ 𝒰.glueMorphisms u hglue = mOf ρ := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ g.q.left) _ _ fun i => ?_
    change pullback.fst g.q.left (𝒰.f i) ≫ g.q.left ≫ 𝒰.glueMorphisms u hglue =
      pullback.fst g.q.left (𝒰.f i) ≫ mOf ρ
    have hι : 𝒰.f i ≫ 𝒰.glueMorphisms u hglue = u i := Scheme.Cover.ι_glueMorphisms 𝒰 u hglue i
    rw [pullback.condition_assoc, hι]
    exact hu i
  refine ⟨fnOf (𝒰.glueMorphisms u hglue), ?_⟩
  rw [← fnOf_comp, hU, fnOf_mOf]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
