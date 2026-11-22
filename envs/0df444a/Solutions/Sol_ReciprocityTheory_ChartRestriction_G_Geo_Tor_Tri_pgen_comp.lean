-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Tri.pgen_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:39.223226+00:00
-- url     : https://prove2.me/submissions/9449fa6f-35de-4666-a06d-ae063ab80463

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
theorem _root_.solution (T : Tri w w' w'') (hL' : L'.IsLB) (hw : PGen w) (hw' : PGen w') : PGen w'' := by
  have key : ∀ {G : Type _} [CommGroup G] (b c p q : G), b * 1⁻¹ * p * (1 * c⁻¹ * q) = b * c⁻¹ * (p * q) := by
    intro G _ b c p q
    simp only [inv_one, mul_one, one_mul]
    exact mul_mul_mul_comm _ _ _ _
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨i, hi⟩ := exists_chart hL' (F' (f y))
  rw [T Y f y j i k hj hi hk, T Y f y j' i k' hj' hi hk',
    hw Y (f ≫ F') y j j' i i hj hj' hi hi, hw' Y f y i i k k' hi hi hk hk',
    gm_self hL' (f ≫ F') y hi, Category.assoc]
  exact key _ _ _ _
end Tri
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
