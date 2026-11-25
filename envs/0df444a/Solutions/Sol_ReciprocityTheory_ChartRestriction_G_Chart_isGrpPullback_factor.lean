-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:46.750513+00:00
-- url     : https://prove2.me/submissions/34b42f44-bc1d-4446-a890-7ca01aa868be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr


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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by
  have hfst : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.fst G.hom f = F := pullback.lift_fst _ _ _
  have hsnd : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.snd G.hom f = G''.hom ≫ g := pullback.lift_snd _ _ _
  have hP := Geo.Tor.isGrpPullback_pullback G f
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback G.hom f)
    rw [hfst]
    exact h.1
  · intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · let x₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (x₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w x₀))
      let y₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (y₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w y₀))
      let x₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (x.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w x) =≫ (g ≫ f))
      let y₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (y.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w y) =≫ (g ≫ f))
      have e1 : (x₀' * y₀').left = (x₀ * y₀).left ≫ pullback.fst G.hom f :=
        hP.2 _ x₀ y₀ x₀' y₀' rfl rfl
      have e2 : (x₀'' * y₀'').left = (x * y).left ≫ F := h.2 T x y x₀'' y₀'' rfl rfl
      have e3 : (x₀' * y₀').left = (x₀'' * y₀'').left := by
        refine Geo.Tor.mul_left_congr (Category.assoc T.hom g f) x₀' y₀' x₀'' y₀'' ?_ ?_
        · show x₀.left ≫ pullback.fst G.hom f = x.left ≫ F
          rw [hx, Category.assoc, hfst]
        · show y₀.left ≫ pullback.fst G.hom f = y.left ≫ F
          rw [hy, Category.assoc, hfst]
      rw [Category.assoc, hfst, ← e1, e3, e2]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x * y)]
      exact Over.w (x₀ * y₀)
end ReciprocityTheory.ChartRestriction.G.Chart
