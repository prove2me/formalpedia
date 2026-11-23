-- Prove2me | solution 1 for ReciprocityTheory.Gal.unramOutside_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:56.713449+00:00
-- url     : https://prove2.me/submissions/f40b89df-f061-4eec-b909-d203c5c8329f

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
namespace ReciprocityTheory.Gal
theorem _root_.solution {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    (ρ : G F Ω →* H) (hρ : Continuous ρ) :
    UnramOutside S ρ ↔ ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia (F := F) A, ρ σ = 1 := by
  constructor
  · intro h v hv A hA σ hσ
    apply h
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]
    exact ⟨v, hv, A, hA, hσ⟩
  · intro h σ hσ
    have hker : NS Ω S ≤ ρ.ker := by
      apply Subgroup.topologicalClosure_minimal
      · apply Subgroup.normalClosure_le_normal
        intro τ hτ
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hτ
        obtain ⟨v, hv, A, hA, hτ⟩ := hτ
        exact MonoidHom.mem_ker.mpr (h v hv A hA τ hτ)
      · rw [MonoidHom.coe_ker]
        exact isClosed_singleton.preimage hρ
    exact MonoidHom.mem_ker.mp (hker hσ)
end ReciprocityTheory.Gal
