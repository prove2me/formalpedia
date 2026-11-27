-- Prove2me | solution 1 for PositivityTheory.PTNLoc.locHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:33.965142+00:00
-- url     : https://prove2.me/submissions/ede548a7-4bf5-475c-8cc7-8c436589e80d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_MemDecompositionSubgroupIff
import Theorems.Thm_PositivityTheory_PTNLoc_mem_decompositionSubgroup_iff
import Theorems.Thm_PositivityTheory_PTNLoc_valuation_le_one_transport
import Theorems.Thm_PositivityTheory_PTNLoc_valuation_lt_one_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise
open PositivityTheory PositivityTheory.PTNLoc
namespace PositivityTheory.PTNLoc
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ A A' hA σ
  have hdec : σ ∈ A.decompositionSubgroup F ↔ Φ σ ∈ A'.decompositionSubgroup F' := by
    rw [mem_decompositionSubgroup_iff, mem_decompositionSubgroup_iff]
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, hA, hA]
      exact h x
    · intro h x
      have := h (E x)
      rwa [hΦ, hA, hA] at this
  refine ⟨hdec, ?_, fun q => ?_⟩
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_sub E, valuation_lt_one_transport E hA] at this
  · show (σ ∈ A.decompositionSubgroup F ∧ _) ↔ (Φ σ ∈ A'.decompositionSubgroup F' ∧ _)
    refine and_congr hdec ⟨fun h y hy => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := E.surjective y
      rw [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA]
      exact h x ((valuation_le_one_transport E hA x).1 hy)
    · have := h (E x) ((valuation_le_one_transport E hA x).2 hx)
      rwa [hΦ, ← map_pow E x q, ← map_sub E, valuation_lt_one_transport E hA] at this
end PositivityTheory.PTNLoc
