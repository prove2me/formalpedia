-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_blowup_of_eq_on_open_2be0684b2feb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:21.78601+00:00
-- url     : https://prove2.me/submissions/07253ffe-f7da-44ef-9083-911ad50f7197

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_hom_ext_of_sup_eq_top_2e3e6019c0a7
import Theorems.Thm_GlobalTheory_Principalise_effCartier_comap_of_disjoint
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
namespace GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
theorem _root_.solution : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens),
    FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) →
    FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by
  intro X₁ X₂ π Z Z' O₁ O₂ hB hO h₁ h₂ hC
  have hiso := isIso_restrict_of_effCartier hB O₂ hC
  have cov : ∀ {W : Scheme.{0}} (g : W ⟶ X₁) (w : W), w ∈ g ⁻¹ᵁ O₁ ∨ w ∈ g ⁻¹ᵁ O₂ := by
    intro W g w
    have : g w ∈ O₁ ⊔ O₂ := by rw [hO]; trivial
    exact this
  have eq₁ : ∀ {W : Scheme.{0}} (g : W ⟶ X₁),
      Z'.comap ((g ⁻¹ᵁ O₁).ι ≫ g) = Z.comap ((g ⁻¹ᵁ O₁).ι ≫ g) := fun g =>
    comap_eq_of_factor h₁ _ (g ∣_ O₁) (morphismRestrict_ι g O₁)
  refine ⟨effCartier_of_forall_mem _ fun x => ?_, fun W g hg => ?_⟩
  · rcases cov π x with hx | hx
    · refine ⟨π ⁻¹ᵁ O₁, hx, ?_⟩
      rw [← Scheme.IdealSheafData.comap_comp, eq₁, Scheme.IdealSheafData.comap_comp]
      exact effCartier_comap_of_isOpenImmersion' _ _ hB.1
    · refine ⟨π ⁻¹ᵁ O₂, hx, ?_⟩
      rw [← Scheme.IdealSheafData.comap_comp]
      exact Principalise.effCartier_comap_of_disjoint _ _ fun w => h₂ _ w.2
  · have c₁ : FinalTheorems.EffCartier (Z.comap ((g ⁻¹ᵁ O₁).ι ≫ g)) := by
      rw [← eq₁, Scheme.IdealSheafData.comap_comp]
      exact effCartier_comap_of_isOpenImmersion' _ _ hg
    obtain ⟨σ₁, hσ₁, hu₁⟩ := hB.2 _ _ c₁
    have hσ₁' : σ₁ ≫ π = (g ⁻¹ᵁ O₁).ι ≫ g := hσ₁
    let σ₂ : (g ⁻¹ᵁ O₂).toScheme ⟶ X₂ := (g ∣_ O₂) ≫ inv (π ∣_ O₂) ≫ (π ⁻¹ᵁ O₂).ι
    have hσ₂ : σ₂ ≫ π = (g ⁻¹ᵁ O₂).ι ≫ g := by
      simp only [σ₂, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    have hW : g ⁻¹ᵁ O₁ ⊔ g ⁻¹ᵁ O₂ = ⊤ := eq_top_iff.2 fun w _ => cov g w
    obtain ⟨s, hs₁, hs₂⟩ := exists_glue (g ⁻¹ᵁ O₁) (g ⁻¹ᵁ O₂) hW σ₁ σ₂ (by
      intro T a b _ hab
      have hc : FinalTheorems.EffCartier (Z.comap (a ≫ (g ⁻¹ᵁ O₁).ι ≫ g)) := by
        rw [Scheme.IdealSheafData.comap_comp]
        exact effCartier_comap_of_isOpenImmersion' _ _ c₁
      obtain ⟨_, -, hu⟩ := hB.2 _ _ hc
      refine (hu _ (by beta_reduce; rw [Category.assoc, hσ₁'])).trans (hu _ ?_).symm
      beta_reduce
      rw [Category.assoc, hσ₂, ← Category.assoc, ← hab, Category.assoc])
    refine ⟨s, ?_, fun t ht => ?_⟩
    · refine hom_ext_of_sup_eq_top _ _ hW _ _ ?_ ?_
      · rw [← Category.assoc, hs₁, hσ₁']
      · rw [← Category.assoc, hs₂, hσ₂]
    · have ht' : t ≫ π = g := ht
      refine hom_ext_of_sup_eq_top _ _ hW _ _ ?_ ?_
      · rw [hs₁]; exact hu₁ _ (by beta_reduce; rw [Category.assoc, ht'])
      · rw [hs₂]
        exact eq_of_isIso_restrict _ (g ∣_ O₂) (by rw [morphismRestrict_ι, Category.assoc, ht'])
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
