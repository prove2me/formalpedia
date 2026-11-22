-- Prove2me | solution 1 for ReciprocityTheory.Gal.continuousSMul_intCl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:18.445108+00:00
-- url     : https://prove2.me/submissions/55c1ffb3-99c8-46ac-9da9-f818d87559c7

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply


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
variable (F Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  refine ⟨continuous_discrete_rng.mpr fun c => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g₀, b₀⟩ h
  refine ⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_,
    (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩
  rintro ⟨g, b⟩ ⟨hg, hb⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
  rw [← h]
  exact Subtype.ext hg
end ReciprocityTheory.Gal
