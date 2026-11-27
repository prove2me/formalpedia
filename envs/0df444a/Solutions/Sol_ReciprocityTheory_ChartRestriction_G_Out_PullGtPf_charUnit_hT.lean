-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.charUnit_hT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:18.160789+00:00
-- url     : https://prove2.me/submissions/28a429da-4bed-434f-becd-5aca3a619129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_specMap_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_appTop_eq_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
open Semi Geo.Tor
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)
variable {φ hφ e}
variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)
namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
theorem _root_.solution (χ : X') :
    (hT hφ e xe).appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X (xe χ)).val =
      (charUnit (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X' χ).val := by
  have hfst : hT hφ e xe ≫ TorusInj.tFst (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X =
      TorusInj.tFst (S := Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X' ≫
        Spec.map (CommRingCat.ofHom (ψR xe)) := pullback.lift_fst _ _ _
  have m : (TorusInj.tFst (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).appLE ⊤ ⊤ (TorusInj.tle _) ≫
      (hT hφ e xe).appTop =
      (Spec.map (CommRingCat.ofHom (ψR xe))).appTop ≫
        (TorusInj.tFst (S := Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X').appLE ⊤ ⊤
          (TorusInj.tle _) := by
    rw [appTop_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact (TorusInj.appLE_of_eq hfst _).trans ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm.trans
      (congrArg (· ≫ _) (appTop_eq_appLE _).symm))
  have n := specMap_inv (CommRingCat.ofHom (ψR xe))
  have hs : ψR xe (AddMonoidAlgebra.single (xe χ) 1) = AddMonoidAlgebra.single χ 1 := by
    show AddMonoidAlgebra.mapDomainBialgHom ZU.{0} xe.symm.toAddMonoidHom _ = _
    rw [AddMonoidAlgebra.mapDomainBialgHom_single]
    simp
  refine (congrArg _ (TorusInj.charUnit_val (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (X := X)
    (xe χ))).trans ?_
  refine (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom
    (AddMonoidAlgebra.single (xe χ) 1))) m).trans ?_
  refine (congrArg (fun x => ((TorusInj.tFst (S := Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))))
    X').appLE ⊤ ⊤ (TorusInj.tle _)).hom x)
    (congrArg (fun f => f.hom (AddMonoidAlgebra.single (xe χ) 1)) n)).trans ?_
  refine Eq.trans ?_ (TorusInj.charUnit_val (S := Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) (X := X') χ).symm
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [hs]
end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
