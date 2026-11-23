-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:43.253136+00:00
-- url     : https://prove2.me/submissions/a3475968-3296-4688-b1d5-68bbe2e3ccf8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j k : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gm f y _ (L.g i j) * gm f y _ (L.g j k) = gm f y _ (L.g i k) := by
  have hijk : f y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hi, hj⟩, hk⟩
  rw [← gm_res f y (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hijk,
    ← map_mul, hL.cocycle]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
