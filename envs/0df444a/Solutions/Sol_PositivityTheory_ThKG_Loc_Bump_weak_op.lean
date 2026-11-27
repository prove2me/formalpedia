-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.weak_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:45.264597+00:00
-- url     : https://prove2.me/submissions/41d5ae26-badf-4929-a01f-43943ab802c6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
import Theorems.Thm_P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_cont_seminorm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_eq_of_weak

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {α : Type} [MeasurableSpace α] (μ : Measure α) (G : α → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ))
    (hex : ∀ f, ∃ g : 𝓢(V₁, ℂ), ∀ T : 𝓢(V₁, ℂ) →L[ℂ] ℂ, Integrable (fun a => T (G a f)) μ ∧ T g = ∫ a, T (G a f) ∂μ)
    (hb : ∀ k j : ℕ, ∃ (p : Seminorm ℂ 𝓢(V, ℂ)) (h : α → ℝ), Continuous p ∧ Integrable h μ ∧
      ∀ a f, SchwartzMap.seminorm ℂ k j (G a f) ≤ p f * h a) :
    ∃ L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ), ∀ f (T : 𝓢(V₁, ℂ) →L[ℂ] ℂ), Integrable (fun a => T (G a f)) μ ∧ T (L f) = ∫ a, T (G a f) ∂μ := by
  choose g hg using hex
  let L : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V₁, ℂ) :=
    { toFun := g
      map_add' := fun a b => eq_of_weak fun T => by
        rw [map_add, (hg _ T).2, (hg _ T).2, (hg _ T).2, ← integral_add (hg _ T).1 (hg _ T).1]
        simp
      map_smul' := fun c a => eq_of_weak fun T => by
        rw [map_smul, (hg _ T).2, (hg _ T).2, ← integral_smul]
        simp }
  refine ⟨⟨L, ?_⟩, hg⟩
  refine (schwartz_withSeminorms ℂ V₁ ℂ).continuous_of_continuous_comp L fun i => ?_
  obtain ⟨p, h, hp, hh, hle⟩ := hb i.1 i.2
  refine Seminorm.continuous_of_le (p := (schwartzSeminormFamily ℂ V₁ ℂ i).comp L) (q := (∫ a, h a ∂μ).toNNReal • p)
    (hp.const_smul _) fun f => ?_
  obtain ⟨T, h1, h2⟩ := norming' _ (cont_seminorm (V := V₁) i.1 i.2) (g f)
  change SchwartzMap.seminorm ℂ i.1 i.2 (g f) ≤ ((∫ a, h a ∂μ).toNNReal : ℝ) * p f
  rw [← h1, (hg f T).2]
  calc ‖∫ a, T (G a f) ∂μ‖ ≤ ∫ a, p f * h a ∂μ :=
        norm_integral_le_of_norm_le (hh.const_mul _) (Eventually.of_forall fun a => (h2 _).trans (hle a f))
    _ = (∫ a, h a ∂μ) * p f := by rw [integral_const_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (apply_nonneg _ _)
end PositivityTheory.ThKG.Loc.Bump
