-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.unf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:29:40.957448+00:00
-- url     : https://prove2.me/submissions/bad03706-66b5-4f2f-b601-bfca744db91a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_Nuabs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ Γ' _ hle 𝓕 h𝓕 Q r hr hu
  let ρ : Q → Γ := fun q => ⟨r q, hr q⟩
  have key : ∀ (g g' : Γ') q q', g * r q = g' * r q' → q = q' := fun g g' q q' e =>
    (hu _ (Γ.mul_mem (hle g.2) (hr q))).unique (by simp) (by rw [e]; simp)
  have hinj : Function.Injective ρ := fun q q' e => key 1 1 q q' (congrArg (fun x : Γ => ((1 : Γ') : G) * x) e)
  have := hinj.countable
  have hn : ∀ q, NullMeasurableSet (ρ q • 𝓕) μ := fun q => h𝓕.nullMeasurableSet_smul _
  refine ⟨⋃ q, ρ q • 𝓕, ⟨NullMeasurableSet.iUnion hn, h𝓕.ae_covers.mono fun x ⟨γ, hγ⟩ => ?_, fun g g' hne => ?_⟩,
    fun f hf => ?_⟩
  · obtain ⟨q, hq, -⟩ := hu _ γ⁻¹.2
    refine ⟨⟨_, hq⟩⁻¹, Set.mem_iUnion.2 ⟨q, _, hγ, ?_⟩⟩
    simp [ρ, Subgroup.smul_def, mul_assoc]
  · have e : ∀ (g : Γ') q, g • ρ q • 𝓕 = (⟨g * r q, Γ.mul_mem (hle g.2) (hr q)⟩ : Γ) • 𝓕 := fun g q =>
      smul_smul (g : G) (r q) 𝓕
    simp only [Function.onFun, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff, e]
    refine fun q q' => h𝓕.aedisjoint fun h => hne ?_
    have h1 := congrArg Subtype.val h
    obtain rfl := key _ _ _ _ h1
    exact Subtype.ext (mul_right_cancel h1)
  · rw [lintegral_iUnion₀ hn (h𝓕.aedisjoint.comp_of_injective hinj),
      lintegral_tsum (f := fun q h => f (r q * h)) fun q => (hf.comp (measurable_const_mul (r q))).aemeasurable]
    exact tsum_congr fun q => (measurePreserving_mul_left μ (r q)).setLIntegral_comp_emb
      (measurableEmbedding_mulLeft _) f 𝓕
end PositivityTheory.PlacePermOperatorBicommutantSpan
