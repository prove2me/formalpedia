-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:11:30.382149+00:00
-- url     : https://prove2.me/submissions/4c476a02-89d0-4c7e-9e6e-2d0ed2cad5b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_grpT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_grpT


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
variable (i : splitTorus S X ⟶ G)
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution [IsMonHom i] : IsMonHom (iB f X i) := by
  have gG := isGrpPullback_pullback G f
  have gT := grpT f X
  have key : ∀ (T : Over S') (x y : T ⟶ splitTorus S' X),
      (x * y) ≫ iB f X i = (x ≫ iB f X i) * (y ≫ iB f X i) := by
    intro T x y
    apply Over.OverMorphism.ext
    refine gG.1.hom_ext ?_ ?_
    · let x₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X := Over.homMk (x.left ≫ hT f X) (by
        rw [Category.assoc, hT_snd, ← Category.assoc, Over.w x] <;> rfl)
      let y₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X := Over.homMk (y.left ≫ hT f X) (by
        rw [Category.assoc, hT_snd, ← Category.assoc, Over.w y] <;> rfl)
      have e1 := gT.2 T x y x₀ y₀ rfl rfl
      have e2 := gG.2 T (x ≫ iB f X i) (y ≫ iB f X i) (x₀ ≫ i) (y₀ ≫ i)
        (by
          show (x.left ≫ hT f X) ≫ i.left = (x ≫ iB f X i).left ≫ pullback.fst G.hom f
          simp only [Over.comp_left, Category.assoc, iB_h])
        (by
          show (y.left ≫ hT f X) ≫ i.left = (y ≫ iB f X i).left ≫ pullback.fst G.hom f
          simp only [Over.comp_left, Category.assoc, iB_h])
      calc ((x * y) ≫ iB f X i).left ≫ pullback.fst G.hom f
          = (x * y).left ≫ hT f X ≫ i.left := by rw [Over.comp_left, Category.assoc, iB_h]
        _ = ((x₀ * y₀) ≫ i).left := by rw [Over.comp_left, e1, Category.assoc]
        _ = ((x₀ ≫ i) * (y₀ ≫ i)).left := by
          congr 1
          first
          | simp
          | (rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc]
             congr 1
             simp)
        _ = ((x ≫ iB f X i) * (y ≫ iB f X i)).left ≫ pullback.fst G.hom f := e2
    · simp only [Over.w]
  refine ⟨?_, ?_⟩
  · have h1 := key (𝟙_ (Over S')) 1 1
    rw [_root_.mul_one] at h1
    have h3 : (1 ≫ iB f X i) * (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G) =
        (1 ≫ iB f X i) * (1 ≫ iB f X i) := by
      rw [_root_.mul_one]
      exact h1
    have h2 := (mul_left_cancel h3).symm
    have e : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [← e, ← e]
    exact h2
  · have h1 := key _ (fst (splitTorus S' X) (splitTorus S' X)) (snd (splitTorus S' X) (splitTorus S' X))
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
