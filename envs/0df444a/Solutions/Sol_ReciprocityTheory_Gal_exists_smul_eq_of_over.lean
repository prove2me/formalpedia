-- Prove2me | solution 1 for ReciprocityTheory.Gal.exists_smul_eq_of_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:18.392663+00:00
-- url     : https://prove2.me/submissions/b0d7ae11-d669-464a-ba0c-ebf6c879124b

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_under_primeBelow
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal)
    (hA' : ∀ x : 𝓞 F, A'.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ g : Ω ≃ₐ[F] Ω, g • A = A' := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by rw [under_primeBelow hA, under_primeBelow hA'])
  refine ⟨g, eq_of_valuation_lt_one_iff F fun b hb => ?_⟩
  let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
  change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
  rw [primeBelow_smul, hg]
end ReciprocityTheory.Gal
