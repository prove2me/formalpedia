-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:57.901807+00:00
-- url     : https://prove2.me/submissions/703551e8-3cdf-4885-88a4-7cf277ca5d10

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
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
omit hJ
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) : val (LB.invGen L φ ε t) r z J = (val t r z J)⁻¹ := by
  simp only [val, LB.invGen]
  exact map_inv _ _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
