-- Prove2me | solution 1 for P2M_GlobalTheory_ExpCmp_fam_B_comp_5fb0830a2fdc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:36:11.13153+00:00
-- url     : https://prove2.me/submissions/6394b83d-3a79-48da-add1-c8a13bcefae2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
namespace GlobalTheory.ExpCmp
theorem _root_.solution {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by
  have push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left
    rw [Category.assoc, hc, Category.assoc])
  let ρ := pushHom pb D'.P.A (𝟙 _)
  have hρ : ρ.left = β := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α) := by
      rw [map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α := by rw [push, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
end GlobalTheory.ExpCmp
