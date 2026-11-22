-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.mul_left_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:10.260212+00:00
-- url     : https://prove2.me/submissions/d1a32136-3366-453c-846f-fe727520f6e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp

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
theorem _root_.solution {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left) :
    (x * y).left = (x' * y').left := by
  subst h
  have e1 : x = x' := Over.OverMorphism.ext hx
  have e2 : y = y' := Over.OverMorphism.ext hy
  subst e1 e2
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
