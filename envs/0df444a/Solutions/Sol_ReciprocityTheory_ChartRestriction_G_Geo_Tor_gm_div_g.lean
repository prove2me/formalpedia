-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:50.7964+00:00
-- url     : https://prove2.me/submissions/b9fb3f57-f98c-4122-90c3-03ce7a679a5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

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
theorem _root_.solution (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι) (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j')
    (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k'))
      ((LB.div (L.pull F) L').g (fun _ => j, k) (fun _ => j', k')) =
      gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ := by
  have hW : f y ∈ ((L.pull F).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull F).U (fun _ => j') ⊓ L'.U k')) :=
    ⟨⟨mem_pull (J := fun _ => j) |>.2 hj, hk⟩, ⟨mem_pull (J := fun _ => j') |>.2 hj', hk'⟩⟩
  dsimp only [LB.div]
  rw [map_mul, map_inv]
  erw [gm_res f y _ hW, gm_res f y _ hW]
  congr 1
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique, zpow_one]
  have h1 : f y ∈ LB.wchart L (fun _ : PUnit => F) (fun _ => j) ⊓ LB.wchart L (fun _ : PUnit => F) (fun _ => j') :=
    ⟨mem_pull (J := fun _ => j) |>.2 hj, mem_pull (J := fun _ => j') |>.2 hj'⟩
  erw [gm_res f y _ h1,
    gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
