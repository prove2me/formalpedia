-- Prove2me | solution 1 for P2M_GlobalTheory_GtTorsionPoints_gt__eq_3132c75b5ca1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:55.380499+00:00
-- url     : https://prove2.me/submissions/5e2b4f0b-e5c2-46f6-a1ed-f921449dda9b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralOfTorsion
import Theorems.Thm_GlobalTheory_GtTorsionPoints_cF_eq
import Theorems.Thm_GlobalTheory_GtTorsionPoints_zeroF_eq
import Theorems.Thm_GlobalTheory_GtTorsionPoints_padd_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GtTorsionPoints
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T)
namespace GlobalTheory.GtTorsionPoints
theorem _root_.solution (b : T ⟶ D.P.A) {b' : TF (R := R) F ⟶ D.P.A} (hb : b' = ρ ≫ b) (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F b' χ k = ρ.left ≫ DegPre.gtφT D T b χ k := by
  subst hb
  fin_cases k
  · change (padd D.P.A (DegPre.cF D F χ) (ρ ≫ b)).left = (ρ ≫ padd D.P.A (DegPre.cT D T χ) b).left
    rw [cF_eq D ρ, padd_comp]
  · change (DegPre.cF D F χ).left = (ρ ≫ DegPre.cT D T χ).left
    rw [cF_eq D ρ]
  · rfl
  · change (DegPre.zeroF D F).left = (ρ ≫ DegPre.zeroT D T).left
    rw [zeroF_eq D ρ]
end GlobalTheory.GtTorsionPoints
