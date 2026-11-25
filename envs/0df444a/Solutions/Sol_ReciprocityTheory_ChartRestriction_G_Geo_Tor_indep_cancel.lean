-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.indep_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:53.348346+00:00
-- url     : https://prove2.me/submissions/54c1c30f-2258-4a09-aa54-a7c936c6a6a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self

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
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w) (hw'' : PGen w'')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j j' : L.ι) (i : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hj' : F (F' (f y)) ∈ L.U j') (hi : F' (f y) ∈ L'.U i) (hk : f y ∈ L''.U k) :
    (gw w (f ≫ F') y j i)⁻¹ * gw w'' f y j k = (gw w (f ≫ F') y j' i)⁻¹ * gw w'' f y j' k := by
  have e1 := hw Y (f ≫ F') y j j' i i hj hj' hi hi
  have e2 := hw'' Y f y j j' k k hj hj' hk hk
  rw [e1, e2, gm_self hL' (f ≫ F') y hi, gm_self hL'' f y hk]
  simp only [inv_one, mul_one, Category.assoc]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
