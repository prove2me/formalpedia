-- Prove2me | solution 1 for P2M_GlobalTheory_BiextSym_val_pull__289846acbbfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:05.43296+00:00
-- url     : https://prove2.me/submissions/c9bef729-aedb-4ffb-91b0-2dc09b594ccc

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.BiextSym
theorem _root_.solution {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]
end GlobalTheory.BiextSym
