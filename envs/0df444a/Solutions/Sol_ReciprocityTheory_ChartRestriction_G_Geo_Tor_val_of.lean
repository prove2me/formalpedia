-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:30.078779+00:00
-- url     : https://prove2.me/submissions/f1421b08-14df-41f4-9b72-259a961d83a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    val t r z J = gm r z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
