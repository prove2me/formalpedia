-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isPullCubical_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:29.288412+00:00
-- url     : https://prove2.me/submissions/4e2ea0a6-2e7d-4ff1-a469-3a1568938c10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (m : CubeMap G' G) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') :
    m.IsPullCubical c' c ↔ ∃ w : LB.Iso L'.L (L.L.pull m.F), PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e ∧
      PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3 := by
  unfold CubeMap.IsPullCubical
  refine exists_congr fun w => and_congr (isGen_iff w) (and_congr ?_ ?_)
  · exact maps_iff w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e
      (m.rigPull L.L L.rig) (fun j => rigPull_le m.F m.e m.e_comm L.L j) (fun j => rfl)
  · exact maps_iff w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3
      (m.thetaPull L.L c.t) (fun j => m.theta_le L.L j) (fun j => rfl)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
