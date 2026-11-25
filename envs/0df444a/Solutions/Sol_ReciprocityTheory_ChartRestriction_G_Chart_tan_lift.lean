-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:15:30.896068+00:00
-- url     : https://prove2.me/submissions/47087d67-8673-4d4e-83fe-1617ea4759d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_derOf_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofLin_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofLin_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLocalizedModule_tan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (h' : B →ₐ[S] DualNumber A') (hh' : IsTanAt ((IsScalarTower.toAlgHom S A A').comp e) h') :
    ∃ m ∈ M, ∃ h : B →ₐ[S] DualNumber A, IsTanAt e h ∧
      (dualMapS (IsScalarTower.toAlgHom S A A')).comp h = (scaleS (algebraMap S A' m)).comp h' := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  have : IsScalarTower S B A' := ⟨fun r b a => by
    show ι (e (r • b)) * a = r • (ι (e b) * a)
    rw [map_smul, map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  have hsm'' : ∀ (b : B) (a : A'), b • a = (ι.comp e) b * a := fun _ _ => rfl
  let g' := (derOf (ι.comp e) hsm'' h' hh').liftKaehlerDifferential
  obtain ⟨g, ⟨_, ⟨m, hm, rfl⟩⟩, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g'
  refine ⟨m, hm, ofLin e hsm g, fun b => ofLin_fst e hsm g b, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst, scaleS_fst, ofLin_fst, hh']
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd, scaleS_snd, ofLin_snd]
    have := LinearMap.congr_fun hg (KaehlerDifferential.D S B b)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    refine this.trans ?_
    show (algebraMap S B m) • g' (KaehlerDifferential.D S B b) = _
    rw [hsm', Derivation.liftKaehlerDifferential_comp_D, derOf_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
