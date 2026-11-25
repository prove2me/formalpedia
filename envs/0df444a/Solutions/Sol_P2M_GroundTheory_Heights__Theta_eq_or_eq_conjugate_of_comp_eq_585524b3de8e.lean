-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:21.0046+00:00
-- url     : https://prove2.me/submissions/17aae518-31f2-46c4-852f-f55b039b8536

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_not_mem_range_b45f5fd1c0af
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ringHom_ext_of_not_mem_a2804716ddc4
import Theorems.Thm_GroundTheory_Automorphic_add_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (φ ψ : E →+* ℂ)
    (h : φ.comp (algebraMap F E) = ψ.comp (algebraMap F E)) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  obtain ⟨a, ha⟩ := exists_not_mem_range (F := F) (E := E)
  have hF : ∀ c, φ (algebraMap F E c) = ψ (algebraMap F E c) := fun c =>
    congrArg (fun f : F →+* ℂ => f c) h
  have hquad : ∀ χ : E →+* ℂ, χ a * χ a - χ (algebraMap F E (Algebra.trace F E a)) * χ a +
      χ (algebraMap F E (Algebra.norm F a)) = 0 := by
    intro χ
    rw [← mul_conj (F := F) a, ← add_conj (F := F) a]
    simp only [map_mul, map_add]
    ring
  have hφ := hquad φ
  have hψ := hquad ψ
  rw [← hF, ← hF] at hψ
  have hfac : (ψ a - φ a) * (ψ a - (φ (algebraMap F E (Algebra.trace F E a)) - φ a)) = 0 := by
    linear_combination hψ - hφ
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    exact (ringHom_ext_of_not_mem ha hF (sub_eq_zero.1 h1).symm).symm
  · right
    symm
    refine ringHom_ext_of_not_mem ha (fun c => ?_) ?_
    · rw [ComplexEmbedding.conjugate_coe_eq, embedding_algebraMap_conj, hF]
    · rw [ComplexEmbedding.conjugate_coe_eq, ← embedding_conj F E, sub_eq_zero.1 h1, conj_apply,
        map_sub]
end GroundTheory.Heights₂.Theta
