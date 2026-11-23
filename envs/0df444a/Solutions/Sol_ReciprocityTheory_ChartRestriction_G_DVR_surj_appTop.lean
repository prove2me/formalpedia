-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.surj_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:14.952271+00:00
-- url     : https://prove2.me/submissions/a899715b-ac2f-4152-be08-72a61d526de1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hG : GlobalFnsSt) : Function.Surjective (fst (TF (R := R) F) D.P.A).left.appTop.hom := by
  have hA : IsAbelianScheme (DegPre.BFo D F) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := D.P.isAb.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hb := (hG _ _ hA).2
  have e : (fst (TF (R := R) F) D.P.A).left =
      (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom ≫ pullback.snd D.P.A.hom (DegPre.jFR (R := R) F) :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  have : IsIso (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso
    (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.appTop).2.comp hb
end ReciprocityTheory.ChartRestriction.G.DVR
