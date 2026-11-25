-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.act_nat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:00.685898+00:00
-- url     : https://prove2.me/submissions/49d82272-0c55-4d29-8490-d039b4c166f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_add_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_one_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_zero_apply

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
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}
variable {O : Type} [Ring O] (ρ : RingAct A O)
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (x : T ⟶ A) (n : ℕ) : x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_apply, _root_.pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add_apply, ih, act_one_apply, _root_.pow_succ]
end ReciprocityTheory.ChartRestriction.G.H1
