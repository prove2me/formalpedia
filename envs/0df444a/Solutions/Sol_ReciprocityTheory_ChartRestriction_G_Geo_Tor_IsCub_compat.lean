-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:52.075016+00:00
-- url     : https://prove2.me/submissions/03d05276-3df4-43d8-8dbd-512eede732a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
theorem _root_.solution (x x' y y' : A) :
    θ (x * x') y y' * θ x x' y' * θ x x' y = θ x x' (y * y') * θ x y y' * θ x' y y' := by
  have c1 := h.coc x x' y y'
  have c2 := h.coc x' y y' x
  have e1 : θ x (x' * y) y' = θ (x' * y) y' x := by rw [h.s01 x (x' * y) y', h.s12 (x' * y) x y']
  have e2 : θ x' y x = θ x x' y := by rw [h.s12 x' y x, h.s01 x' x y]
  have e3 : θ x' (y * y') x = θ x x' (y * y') := by rw [h.s12 x' (y * y') x, h.s01 x' x (y * y')]
  have e4 : θ y y' x = θ x y y' := by rw [h.s12 y y' x, h.s01 y x y']
  rw [e2, e3, e4] at c2
  rw [e1] at c1
  calc θ (x * x') y y' * θ x x' y' * θ x x' y = θ (x' * y) y' x * θ x' y y' * θ x x' y := by rw [c1]
    _ = θ (x' * y) y' x * θ x x' y * θ x' y y' := by ac_rfl
    _ = θ x x' (y * y') * θ x y y' * θ x' y y' := by rw [c2]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
