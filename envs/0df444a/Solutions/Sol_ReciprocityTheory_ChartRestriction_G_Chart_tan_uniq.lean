-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:15:32.825798+00:00
-- url     : https://prove2.me/submissions/eebe826f-44f4-4d64-8fad-a70c7b989472

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_derOf_apply
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
theorem _root_.solution (h₁ h₂ : B →ₐ[S] DualNumber A) (t₁ : IsTanAt e h₁) (t₂ : IsTanAt e h₂)
    (heq : (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₁ = (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₂) :
    ∃ m ∈ M, (scaleS (algebraMap S A m)).comp h₁ = (scaleS (algebraMap S A m)).comp h₂ := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  let g₁ := (derOf e hsm h₁ t₁).liftKaehlerDifferential
  let g₂ := (derOf e hsm h₂ t₂).liftKaehlerDifferential
  have hfg : f.comp g₁ = f.comp g₂ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    show f (g₁ (KaehlerDifferential.D S B b)) = f (g₂ (KaehlerDifferential.D S B b))
    simp only [g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply]
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq b)
    simp only [AlgHom.comp_apply, dualMapS_snd] at this
    exact this
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g₁ g₂ hfg
  refine ⟨m, hm, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_fst, scaleS_fst, t₁, t₂]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_snd, scaleS_snd]
    have := LinearMap.congr_fun hc (KaehlerDifferential.D S B b)
    simp only [LinearMap.smul_apply, g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply] at this
    change algebraMap S B m • (h₁ b).snd = algebraMap S B m • (h₂ b).snd at this
    rwa [hsm, hsm, AlgHom.commutes] at this
end ReciprocityTheory.ChartRestriction.G.Chart
