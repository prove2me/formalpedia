-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:22.499087+00:00
-- url     : https://prove2.me/submissions/35d1b105-65b6-48dc-8e9c-09ce581a0dff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div_g

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
theorem _root_.solution (w : LB.Iso L' (L.pull F)) : w.IsGen ↔ PGen w := by
  constructor
  · intro hg Y f y j j' k k' hj hj' hk hk'
    have hW : f y ∈ ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k')) :=
      ⟨⟨mem_pull (J := fun _ => j) |>.2 hj, hk⟩, ⟨mem_pull (J := fun _ => j') |>.2 hj', hk'⟩⟩
    have e := congrArg (gm f y _) (hg (fun _ => j, k) (fun _ => j', k'))
    erw [map_mul, gm_res f y _ hW, gm_res f y _ hW, gm_div_g f y j j' k k' hj hj' hk hk'] at e
    exact e
  · intro hp p q
    apply unit_ext
    intro x hx
    erw [map_mul, gm_res _ _ _ hx, gm_res _ _ _ hx]
    obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩ := hx
    have e := hp X' (𝟙 X') x (p.1 PUnit.unit) (q.1 PUnit.unit) p.2 q.2 (mem_pull.1 hp1) (mem_pull.1 hq1) hp2 hq2
    show gw w (𝟙 X') x (p.1 PUnit.unit) p.2 =
      gm (𝟙 X') x ((L.pull F).U (fun _ => p.1 PUnit.unit) ⊓ L'.U p.2 ⊓
        ((L.pull F).U (fun _ => q.1 PUnit.unit) ⊓ L'.U q.2))
        ((LB.div (L.pull F) L').g (fun _ => p.1 PUnit.unit, p.2) (fun _ => q.1 PUnit.unit, q.2)) *
        gw w (𝟙 X') x (q.1 PUnit.unit) q.2
    rw [e, gm_div_g (𝟙 X') x (p.1 PUnit.unit) (q.1 PUnit.unit) p.2 q.2 (mem_pull.1 hp1) (mem_pull.1 hq1) hp2 hq2]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
