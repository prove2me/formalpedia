-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rv_val_tau_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:00.441946+00:00
-- url     : https://prove2.me/submissions/07bb5199-48ec-4795-af22-30b9dccb3d35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValuePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (x : D.toPre.X) {Z : Scheme.{0}} (r : Z ⟶ (TK V).left) (z : Z)
    {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} (hJ : Good D.toPre.P.L z J) :
    val (D.toPre.tau x 0) r z J = (val (D.toPre.psi 0) r z J)⁻¹ * (val D.toPre.rigK r z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.toPre.psi w) r z J) (add_zero x), mul_inv_cancel, _root_.one_mul]
end ReciprocityTheory.ChartRestriction.G.DVR
