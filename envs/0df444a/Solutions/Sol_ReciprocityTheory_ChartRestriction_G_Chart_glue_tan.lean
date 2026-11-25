-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.glue_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:21.285062+00:00
-- url     : https://prove2.me/submissions/51c00d09-e8ac-48c8-9eb0-1e0ddbbe6278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toL_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fromL_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fromL_toL
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (s k)) →+* T)
      (β : DualNumber (Localization.Away (s l)) →+* T), α.comp (dAway (s k)) = β.comp (dAway (s l)) →
      Spec.map (CommRingCat.ofHom α) ≫ (w k).left = Spec.map (CommRingCat.ofHom β) ≫ (w l).left) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  let f : ∀ k, 𝒰.X k ⟶ G.left := fun k => Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left
  have hf : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ f k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ f l := by
    refine fun (k : Fin n) (l : Fin n) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (s k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (s l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber S) (Ld (s k))) = B.hom.comp (algebraMap (DualNumber S) (Ld (s l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (s k))).comp (dAway (s k)) = (B.hom.comp (toL (s l))).comp (dAway (s l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (s k))) (B.hom.comp (toL (s l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s l))) ≫ (w l).left
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  let g := 𝒰.glueMorphisms f hf
  have hι : ∀ k : Fin n, 𝒰.f k ≫ g = f k := fun k => Scheme.Cover.ι_glueMorphisms 𝒰 f hf k
  have hg : ∀ k : Fin n, Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ g = (w k).left := by
    intro k
    have e : Spec.map (CommRingCat.ofHom (dAway (s k))) = Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ 𝒰.f k := by
      show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
    rw [e, Category.assoc, hι k]
    show Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  have hover : g ≫ G.hom = (sp (R₀ := S) (DualNumber S)).hom := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
    rw [← Category.assoc, hι k]
    show (Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber S)))
    rw [Category.assoc, Over.w (w k)]
    show Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber (Localization.Away (s k))))) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← toL_comp, RingHom.comp_assoc]
    congr 1
    refine RingHom.ext fun r => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl', dAway_inl]
  let v : sp (R₀ := S) (DualNumber S) ⟶ G := Over.homMk g hover
  have hres : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := fun k =>
    Over.OverMorphism.ext (hg k)
  refine ⟨v, ?_, hres⟩
  apply Over.OverMorphism.ext
  let 𝒱 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) _ hs).openCover
  refine Scheme.Cover.hom_ext 𝒱 _ _ fun (k : Fin n) => ?_
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
        (spMap (TrivSqZeroExt.fstHom S S S)).left =
      (spMap (TrivSqZeroExt.fstHom S (Localization.Away (s k)) (Localization.Away (s k)))).left ≫
        (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left := by
    rw [spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (dualMapS_fst (Algebra.ofId S (Localization.Away (s k))) x).symm
  have h1 := congrArg (fun q => Over.Hom.left q) (hw k)
  simp only [Over.comp_left] at h1
  show Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      ((spMap (TrivSqZeroExt.fstHom S S S)).left ≫ v.left) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫ (1 : sp (R₀ := S) S ⟶ G).left
  rw [← Category.assoc, e1, Category.assoc]
  have h2 : (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left ≫ v.left = (w k).left :=
    congrArg (fun q => Over.Hom.left q) (hres k)
  rw [h2, h1, one_left', one_left']
  show (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k))))) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap S S)) ≫ _)
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id]
end ReciprocityTheory.ChartRestriction.G.Chart
