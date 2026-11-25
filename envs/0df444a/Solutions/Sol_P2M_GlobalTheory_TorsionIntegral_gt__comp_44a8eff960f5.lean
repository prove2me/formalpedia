-- Prove2me | solution 1 for P2M_GlobalTheory_TorsionIntegral_gt__comp_44a8eff960f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:46.645721+00:00
-- url     : https://prove2.me/submissions/88dcdef4-d3b2-4b3b-a30a-97eb63530a61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution {b' : T ⟶ D.P.A} {b : TF (R := R) F ⟶ D.P.A} (hb : φ ≫ b' = b) (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F b χ k = φ.left ≫ DegPre.gtφT D T b' χ k := by
  have e₀ : cP D _ χ * b = φ ≫ (cP D T χ * b') := by rw [MonObj.comp_mul, comp_cP, hb]
  have e₃ : (1 : TF (R := R) F ⟶ D.P.A) = φ ≫ (1 : T ⟶ D.P.A) := (MonObj.comp_one φ).symm
  fin_cases k
  exacts [congrArg (fun q => q.left) e₀, congrArg (fun q => q.left) (comp_cP D φ χ).symm,
    congrArg (fun q => q.left) hb.symm, congrArg (fun q => q.left) e₃]
end GlobalTheory.TorsionIntegral
