-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:48.565962+00:00
-- url     : https://prove2.me/submissions/9156071e-4aae-42f1-a9e4-362d6878dc93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_inj_over
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (w : epsR S ⟶ G') : IsTangent w ↔
    Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (1 : Over.mk x ⟶ G).left := by
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have hmul : ∀ {T : Over (Sp S)} (a b : T ⟶ G'), pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b :=
    fun {T} a b => Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : ∀ T : Over (Sp S), pushPt h.1.w (1 : T ⟶ G') = 1 := by
    intro T
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have hη : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e := congrArg (fun g => g.left) (hone (Over.mk (𝟙 (Sp S))))
    simp only [pushPt, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e
  have hfa : Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (epsR S).hom = 𝟙 _ := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    all_goals
      ext r
      first
        | (simp [TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp; done)
  let t : Over.mk (𝟙 (Sp S)) ⟶ epsR S :=
    Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom) hfa
  rw [oneL]
  simp only [Over.mk_hom]
  constructor
  · intro hw
    unfold IsTangent at hw
    rw [← Category.assoc, hw, hη]
  · intro hw
    unfold IsTangent
    have key : t ≫ w = 1 := by
      apply inj_over h
      show Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = _
      rw [hw, oneL, Category.assoc, hη]
      simp
    have e := congrArg (fun g => g.left) key
    simp only [Over.comp_left, t, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e
end ReciprocityTheory.ChartRestriction.G.Chart
