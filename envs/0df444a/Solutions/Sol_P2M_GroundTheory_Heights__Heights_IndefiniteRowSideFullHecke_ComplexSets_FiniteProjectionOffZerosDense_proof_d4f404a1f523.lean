-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionOffZerosDense_proof_d4f404a1f523
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:13.007772+00:00
-- url     : https://prove2.me/submissions/26a0d0f4-903a-40b5-8ebb-3f144ab75af1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionOffZerosDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionSheetedClosureEquations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionOffZerosDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteProjectionOffZerosDense
theorem _root_.solution (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement)
    (hCl : FiniteProjectionSheetedClosureEquations.Statement) :
    FiniteProjectionOffZerosDense.Statement := by
  intro σ _ X w d A hX hirr hiso hinj δ hδ hδne
  obtain ⟨ℓ, N, a, δ₀, q, ha, hδ₀, hq, hδ₀ne, hp, hsep, hcoord⟩ := hPF σ X w d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X w d A hX hirr hiso hinj ℓ N a δ₀ q ha hδ₀ hq hδ₀ne hp hsep hcoord
  obtain ⟨m, c, hc, hcY, hcl⟩ := hCl σ X w d A hX hiso hinj (fun y => δ₀ y * δ y) (hδ₀.mul hδ)
    ⟨M, hM, fun y hy hne => hMsh y hy (left_ne_zero_of_mul hne)⟩
  have hcomp : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → AnalyticAt ℂ (fun z => f (A z)) w :=
    fun hf => hf.comp (A.analyticAt w)
  have hnot : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → (¬ ∀ᶠ y in 𝓝 (A w), f y = 0) →
      ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f (A z) = 0 := fun hf hne h => hne (hinj _ hf h)
  have hvan : ∀ k, ∀ᶠ z in 𝓝 w, z ∈ X → c k z = 0 := by
    intro k
    have h1 : ∀ᶠ z in 𝓝 w, z ∈ X → (c k z * δ₀ (A z)) * δ (A z) = 0 := by
      filter_upwards [hcY] with z hz hzX
      by_cases h : δ₀ (A z) * δ (A z) = 0
      · rw [mul_assoc, h, mul_zero]
      · rw [hz hzX h k, zero_mul, zero_mul]
    rcases hirr.2 (fun z => c k z * δ₀ (A z)) (fun z => δ (A z)) ((hc k).mul (hcomp hδ₀)) (hcomp hδ)
      h1 with h2 | h2
    · rcases hirr.2 (c k) (fun z => δ₀ (A z)) (hc k) (hcomp hδ₀) h2 with h3 | h3
      · exact h3
      · exact absurd h3 (hnot hδ₀ hδ₀ne)
    · exact absurd h2 (hnot hδ hδne)
  have hall : ∀ᶠ z in 𝓝 w, z ∈ X → ∀ k, c k z = 0 := by
    filter_upwards [Filter.eventually_all.2 hvan] with z hz hzX k using hz k hzX
  refine ⟨_, hall.and hcl, ?_⟩
  rintro z ⟨hzX, hz1, hz2⟩
  refine closure_mono ?_ (hz2 hzX (hz1 hzX))
  rintro x ⟨hx, hne⟩
  exact ⟨hx, right_ne_zero_of_mul hne⟩
end FiniteProjectionOffZerosDense
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
