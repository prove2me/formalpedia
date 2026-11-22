-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:18.221195+00:00
-- url     : https://prove2.me/submissions/541085e7-57c1-481b-801f-bbfe54d5544a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub

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
variable {X Y Z : Scheme.{0}}
variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {x : X'} {J : PUnit → L.ι} : x ∈ (L.pull F).U J ↔ F x ∈ L.U (J PUnit.unit) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h _ => h⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
