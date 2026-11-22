-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:17.981424+00:00
-- url     : https://prove2.me/submissions/ef33ed52-4790-4b7d-a083-95089c358257

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
    (h' : IsGrpPullback G'' G' g φ') (h : IsGrpPullback G' G f φ) : IsGrpPullback G'' G (g ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, ?_⟩
  intro T x y x₀ y₀ hx hy
  have w' : φ' ≫ G'.hom = G''.hom ≫ g := h'.1.w
  have h1 := h'.2 T x y (pushPt w' x) (pushPt w' y) rfl rfl
  let T' : Over S' := Over.mk (T.hom ≫ g)
  let x₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk x₀.left (by rw [Over.w x₀]; simp [T'])
  let y₁ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk y₀.left (by rw [Over.w y₀]; simp [T'])
  have h2 := h.2 T' (pushPt w' x) (pushPt w' y) x₁ y₁ (by simp [x₁, pushPt, hx]) (by simp [y₁, pushPt, hy])
  have h3 := mul_left_congr (G := G) (Category.assoc T.hom g f) x₁ y₁ x₀ y₀ rfl rfl
  rw [← h3, h2, h1, Category.assoc]
end IsGrpPullback
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
