-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:18.478772+00:00
-- url     : https://prove2.me/submissions/ec9ee18e-bd32-452b-9950-0d35c223f497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (x y : Γ(Z, U)) :
    rs h (x * y) = rs h x * rs h y := map_mul _ x y
end ReciprocityTheory.ChartRestriction.G.DVR
