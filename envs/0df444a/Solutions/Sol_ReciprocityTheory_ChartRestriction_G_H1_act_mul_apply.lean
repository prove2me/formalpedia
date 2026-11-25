-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.act_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:00.931215+00:00
-- url     : https://prove2.me/submissions/6931e629-5f14-4cd8-ae3b-a7c4a17d0d72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair

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
theorem _root_.solution (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by
  rw [ρ.map_mul, Category.assoc]
end ReciprocityTheory.ChartRestriction.G.H1
