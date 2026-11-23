-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.pgen_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:53.234803+00:00
-- url     : https://prove2.me/submissions/fe9e42f4-69dd-40e7-8385-deebec0fc32b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace Tri
theorem _root_.solution (T : Tri w w' w'') (hL : L.IsLB) (hw : PGen w) (hw'' : PGen w'') : PGen w' := by
  have key : ∀ {G : Type _} [CommGroup G] (a d p q : G),
      (1 * a⁻¹ * p)⁻¹ * (1 * d⁻¹ * q) = a * d⁻¹ * (p⁻¹ * q) := by
    intro G _ a d p q
    simp only [one_mul]
    rw [mul_inv_rev, inv_inv, mul_comm p⁻¹ a, mul_mul_mul_comm]
  intro Y f y i i' k k' hi hi' hk hk'
  obtain ⟨j, hj⟩ := exists_chart hL (F (F' (f y)))
  have t1 := inv_mul_eq_iff_eq_mul.mpr (T Y f y j i k hj hi hk)
  have t2 := inv_mul_eq_iff_eq_mul.mpr (T Y f y j i' k' hj hi' hk')
  rw [← t1, ← t2, hw'' Y f y j j k k' hj hj hk hk', hw Y (f ≫ F') y j j i i' hj hj hi hi',
    gm_self hL (f ≫ F' ≫ F) y hj, gm_self hL ((f ≫ F') ≫ F) y hj]
  exact key _ _ _ _
end Tri
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
