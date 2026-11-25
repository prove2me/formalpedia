-- Prove2me | solution 1 for PI.GreenHCLabel.simple_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:23.372703+00:00
-- url     : https://prove2.me/submissions/120e2a41-4525-4c01-87a7-5203a5f43bde

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
import Theorems.Thm_PI_GreenHCLabel_basics_lin_comm
import Theorems.Thm_PI_GreenHCLabel_basics_hom_ext
import Theorems.Thm_PI_GreenHCLabel_basics_mono_of_inj
import Theorems.Thm_PI_GreenHCLabel_basics_inj_of_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
noncomputable section
open PI PI.GreenHCLabel
namespace PI.GreenHCLabel
theorem _root_.solution : SimpleIrr := by
  intro Γ _ τ
  have iso_of_bij : ∀ {σ : FDRep ℂ Γ} (f : σ ⟶ τ), Function.Bijective (basicsLin f) → IsIso f := by
    intro σ f hf
    let e := LinearEquiv.ofBijective (basicsLin f) hf
    let g : τ ⟶ σ := basicsMk e.symm.toLinearMap (fun x => by
      apply LinearMap.ext; intro v
      apply e.injective
      have h1 := congrArg (fun k => k (e.symm v)) (basics_lin_comm f x)
      simp only [LinearMap.comp_apply] at h1
      have h2 : basicsLin f (e.symm v) = v := e.apply_symm_apply v
      rw [h2] at h1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact h1.symm)
    exact ⟨⟨g, basics_hom_ext (LinearMap.ext fun v => e.symm_apply_apply v),
      basics_hom_ext (LinearMap.ext fun v => e.apply_symm_apply v)⟩⟩
  have surj_of_iso : ∀ {σ : FDRep ℂ Γ} (f : σ ⟶ τ) [IsIso f], Function.Surjective (basicsLin f) := by
    intro σ f _ v
    refine ⟨basicsLin (inv f) v, ?_⟩
    have := congrArg (fun k => basicsLin k v) (IsIso.inv_hom_id f)
    exact this
  constructor
  · intro hs
    have hnt : Nontrivial τ := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      have h1 : (𝟙 τ : τ ⟶ τ) = 0 := basics_hom_ext (LinearMap.ext fun v => Subsingleton.elim _ _)
      exact ((Simple.mono_isIso_iff_nonzero (𝟙 τ)).1 inferInstance) h1
    refine ⟨hnt, fun W hW => ?_⟩
    haveI : Mono (basicsIncl τ W hW) := basics_mono_of_inj _ (fun a b h => Subtype.ext h)
    by_cases h0 : basicsIncl τ W hW = 0
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have := congrArg (fun k => basicsLin k (⟨v, hv⟩ : W)) h0
      exact this
    · right
      haveI := (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).2 h0
      rw [Submodule.eq_top_iff']
      intro v
      obtain ⟨w, hw⟩ := surj_of_iso (basicsIncl τ W hW) v
      rw [← hw]
      exact w.2
  · rintro ⟨hnt, hirr⟩
    refine ⟨fun {Y} f _ => ⟨fun hiso h0 => ?_, fun hne => ?_⟩⟩
    · obtain ⟨v, w, hvw⟩ := hnt.exists_pair_ne
      apply hvw
      obtain ⟨a, ha⟩ := surj_of_iso f v
      obtain ⟨b, hb⟩ := surj_of_iso f w
      rw [← ha, ← hb, h0]
      rfl
    · have hR : ∀ g, ∀ v ∈ LinearMap.range (basicsLin f), τ.ρ g v ∈ LinearMap.range (basicsLin f) := by
        rintro g _ ⟨u, rfl⟩
        refine ⟨Y.ρ g u, ?_⟩
        have := congrArg (fun k => k u) (basics_lin_comm f g)
        exact this
      rcases hirr _ hR with h | h
      · exact absurd (basics_hom_ext (by rw [LinearMap.range_eq_bot] at h; exact h)) hne
      · exact iso_of_bij f ⟨basics_inj_of_mono f, LinearMap.range_eq_top.1 h⟩
end PI.GreenHCLabel
