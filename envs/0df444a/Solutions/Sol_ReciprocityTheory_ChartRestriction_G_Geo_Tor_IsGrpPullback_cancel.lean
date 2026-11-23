-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:55.66672+00:00
-- url     : https://prove2.me/submissions/ec5f4e27-39d6-4124-aaa7-c2911efc6934

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace IsGrpPullback
theorem _root_.solution {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ)) (w : φ' ≫ G'.hom = G''.hom ≫ g) :
    IsGrpPullback G'' G' g φ' := by
  refine ⟨IsPullback.of_right n.1 w h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  have hn : (φ' ≫ φ) ≫ G.hom = G''.hom ≫ (g ≫ f) := n.1.w
  have h1 := h.2 (Over.mk (T.hom ≫ g)) x₀ y₀ (pushPt hw x₀) (pushPt hw y₀) rfl rfl
  have h2 := n.2 T x y (pushPt hn x) (pushPt hn y) rfl rfl
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) (pushPt hw x₀) (pushPt hw y₀)
    (pushPt hn x) (pushPt hn y) (by simp [pushPt, hx]) (by simp [pushPt, hy])
  apply h.1.hom_ext
  · rw [← h1, h3, h2, Category.assoc]
  · have a1 := Over.w (x₀ * y₀)
    have a2 := Over.w (x * y)
    rw [a1, Category.assoc, w, ← Category.assoc, a2]
    rfl
end IsGrpPullback
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
