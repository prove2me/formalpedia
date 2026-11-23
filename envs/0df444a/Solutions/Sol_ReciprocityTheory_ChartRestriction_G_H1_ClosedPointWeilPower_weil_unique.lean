-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.weil_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:05.921791+00:00
-- url     : https://prove2.me/submissions/b1e5ac80-098a-4518-b4ab-5006489202db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
theorem _root_.solution (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c c' : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) (hc' : WeilIs P.A P.L k x y c') : c = c' :=
  ((hW S P k T).1 x y hx hy).unique hc hc'
end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
