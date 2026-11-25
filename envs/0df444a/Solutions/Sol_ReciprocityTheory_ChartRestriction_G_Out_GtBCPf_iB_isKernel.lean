-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_isKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:11.397102+00:00
-- url     : https://prove2.me/submissions/d91ac06a-8045-42d5-96b8-615c3e209253

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_grpT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_h
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
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
section Maps
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
variable (i : splitTorus S X ⟶ G)
private lemma toUnit_left_lemma {Y : Scheme.{0}} (A : Over Y) : (toUnit A).left = A.hom := rfl
private lemma unit_hom_lemma_2 {Y : Scheme.{0}} : (𝟙_ (Over Y)).hom = 𝟙 Y := rfl
private lemma one_fst_lemma_3 (T : Over S') :
    (1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (T.hom ≫ f) ⟶ B).left := by
  have gB := isGrpPullback_pullback B f
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B :=
    Over.homMk ((1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f) (by
      calc ((1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f) ≫ B.hom
          = (1 : T ⟶ (Over.pullback f).obj B).left ≫ (pullback.fst B.hom f ≫ B.hom) :=
            Category.assoc _ _ _
        _ = (1 : T ⟶ (Over.pullback f).obj B).left ≫ (pullback.snd B.hom f ≫ f) := by
            rw [pullback.condition]
        _ = ((1 : T ⟶ (Over.pullback f).obj B).left ≫ ((Over.pullback f).obj B).hom) ≫ f :=
            (Category.assoc _ _ _).symm
        _ = T.hom ≫ f := by rw [Over.w])
  have e1 := gB.2 T 1 1 x₀ x₀ rfl rfl
  have h2 : x₀ * x₀ = x₀ * 1 := by
    rw [_root_.mul_one]
    apply Over.OverMorphism.ext
    rw [e1, _root_.mul_one] <;> rfl
  have h3 : x₀ = 1 := mul_left_cancel h2
  exact congrArg Over.Hom.left h3
end Maps
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

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
theorem _root_.solution (hk : IsPullback i (toUnit _) q η[B]) :
    IsPullback (iB f X i) (toUnit _) (qB f q) η[(Over.pullback f).obj B] := by
  have gB := isGrpPullback_pullback B f
  have hone : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := by
    intro M _
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have hw : iB f X i ≫ qB f q = toUnit _ ≫ η[(Over.pullback f).obj B] := by
    apply Over.OverMorphism.ext
    refine gB.1.hom_ext ?_ ?_
    · let h' : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S X :=
        Over.homMk (hT f X) (hT_snd f X)
      calc (iB f X i ≫ qB f q).left ≫ pullback.fst B.hom f
          = (iB f X i).left ≫ ((qB f q).left ≫ pullback.fst B.hom f) := by
            rw [Over.comp_left]
            exact Category.assoc _ _ _
        _ = (iB f X i).left ≫ (pullback.fst G.hom f ≫ q.left) := by rw [qB_h]
        _ = ((iB f X i).left ≫ pullback.fst G.hom f) ≫ q.left := (Category.assoc _ _ _).symm
        _ = (hT f X ≫ i.left) ≫ q.left := by rw [iB_h]
        _ = hT f X ≫ (i ≫ q).left := by rw [Category.assoc, Over.comp_left]
        _ = hT f X ≫ (toUnit _ ≫ η[B]).left := by rw [hk.w]
        _ = (h' ≫ (toUnit _ ≫ η[B])).left := rfl
        _ = ((h' ≫ toUnit _) ≫ η[B]).left := by rw [Category.assoc]
        _ = (toUnit _ ≫ η[B]).left := by rw [toUnit_unique (h' ≫ toUnit _) (toUnit _)]
        _ = (1 : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ B).left := by rw [Hom.one_def]
        _ = (1 : splitTorus S' X ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f :=
            (one_fst_lemma_3 f _).symm
        _ = (toUnit _ ≫ η[(Over.pullback f).obj B]).left ≫ pullback.fst B.hom f := by
            rw [Hom.one_def]
    · simp only [Over.w]
  have hη : η[(Over.pullback f).obj B].left ≫ pullback.fst B.hom f = f ≫ η[B].left := by
    have h1 := one_fst_lemma_3 (B := B) f (𝟙_ (Over S'))
    rw [hone, Hom.one_def, Over.comp_left] at h1
    rw [h1, toUnit_left_lemma]
    show ((𝟙_ (Over S')).hom ≫ f) ≫ η[B].left = f ≫ η[B].left
    rw [unit_hom_lemma_2]
    exact congrArg (fun g => g ≫ η[B].left) (Category.id_comp f)
  have sq1 : IsPullback (hT f X) (toUnit (splitTorus S' X)).left
      (toUnit (splitTorus S X)).left f := by
    rw [toUnit_left_lemma, toUnit_left_lemma]
    exact (grpT f X).1
  have sq2 : IsPullback i.left (toUnit (splitTorus S X)).left q.left η[B].left :=
    IsPullback.map (F := Over.forget S) hk
  have s := sq1.paste_horiz sq2
  have H : IsPullback (iB f X i).left (toUnit (splitTorus S' X)).left (qB f q).left
      η[(Over.pullback f).obj B].left := by
    refine IsPullback.of_right ?_ (by simpa using congrArg Over.Hom.left hw) (qB_sq f q)
    rw [iB_h, hη]
    exact s
  exact IsPullback.of_map (F := Over.forget S') hw H
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
