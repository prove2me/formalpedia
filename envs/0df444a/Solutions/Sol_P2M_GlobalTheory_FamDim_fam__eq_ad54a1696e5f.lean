-- Prove2me | solution 1 for P2M_GlobalTheory_FamDim_fam__eq_ad54a1696e5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:18.610365+00:00
-- url     : https://prove2.me/submissions/dd471b60-84fb-4860-9384-f7263c80eb8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTermBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamDim
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.FamDim
theorem _root_.solution (α : D.X) :
    DegPre.famφ D F α = fun i => (snd (TF (R := R) F) D.P.A).left ≫ DegPre.famφB D α i := by
  funext i
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A _ _).left = (snd (TF (R := R) F) D.P.A ≫ padd D.P.A _ _).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ D.c α).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ D.c α).left
    rw [comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
end GlobalTheory.FamDim
