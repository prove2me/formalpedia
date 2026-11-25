-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_exists_glue_6912ea86c35a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:08.41895+00:00
-- url     : https://prove2.me/submissions/0f458394-22a7-4735-87a5-3fcbdbdca396

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier

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
theorem _root_.solution {W Y : Scheme.{0}} (W₁ W₂ : W.Opens) (h : W₁ ⊔ W₂ = ⊤) (σ₁ : W₁.toScheme ⟶ Y)
    (σ₂ : W₂.toScheme ⟶ Y)
    (hc : ∀ (T : Scheme.{0}) (a : T ⟶ W₁) (b : T ⟶ W₂) [IsOpenImmersion a], a ≫ W₁.ι = b ≫ W₂.ι →
      a ≫ σ₁ = b ≫ σ₂) :
    ∃ s : W ⟶ Y, W₁.ι ≫ s = σ₁ ∧ W₂.ι ≫ s = σ₂ := by
  let U : Bool → W.Opens := fun b => cond b W₁ W₂
  have hU : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff, ← h]
    exact sup_le (le_iSup U true) (le_iSup U false)
  let 𝒰 : W.OpenCover := W.openCoverOfIsOpenCover U hU
  let f : ∀ b : Bool, (U b).toScheme ⟶ Y := fun b => match b with
    | true => σ₁
    | false => σ₂
  haveI : ∀ b : Bool, IsOpenImmersion (𝒰.f b) := fun b => inferInstanceAs (IsOpenImmersion (U b).ι)
  have aux₁ : ∀ {A B C : Scheme.{0}} (p : A ⟶ C) (q : B ⟶ C), IsOpenImmersion q → IsOpenImmersion (pullback.fst p q) :=
    fun _ _ _ => inferInstance
  have aux₂ : ∀ {A B C : Scheme.{0}} (p : A ⟶ C) (q : B ⟶ C), IsOpenImmersion p → IsOpenImmersion (pullback.snd p q) :=
    fun _ _ _ => inferInstance
  have hf : ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ f y := by
    rintro (_ | _) (_ | _)
    · exact congrArg (· ≫ σ₂) ((cancel_mono (𝒰.f false)).1 pullback.condition)
    · exact (@hc _ (pullback.snd (𝒰.f false) (𝒰.f true)) (pullback.fst (𝒰.f false) (𝒰.f true))
        (aux₂ (𝒰.f false) (𝒰.f true) (this false)) pullback.condition.symm).symm
    · exact @hc _ (pullback.fst (𝒰.f true) (𝒰.f false)) (pullback.snd (𝒰.f true) (𝒰.f false))
        (aux₁ (𝒰.f true) (𝒰.f false) (this false)) pullback.condition
    · exact congrArg (· ≫ σ₁) ((cancel_mono (𝒰.f true)).1 pullback.condition)
  exact ⟨𝒰.glueMorphisms f hf, 𝒰.ι_glueMorphisms f hf true, 𝒰.ι_glueMorphisms f hf false⟩
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
