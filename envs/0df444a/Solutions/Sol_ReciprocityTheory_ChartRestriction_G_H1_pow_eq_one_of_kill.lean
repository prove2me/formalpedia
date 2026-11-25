-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.pow_eq_one_of_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:09.116458+00:00
-- url     : https://prove2.me/submissions/1e5e4079-a8fa-41f5-8997-a3ac36b6a92c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_one_compMon
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_mul_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_act_nat_apply

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
theorem _root_.solution {a b : O} {N : ℕ} (hab : a * b = (N : O)) (x : T ⟶ A) (hx : x ≫ ρ.act b = 1) :
    x ^ N = 1 := by
  rw [← act_nat_apply ρ x N, ← hab, act_mul_apply, hx]
  haveI := ρ.hom a
  exact one_compMon (ρ.act a)
end ReciprocityTheory.ChartRestriction.G.H1
