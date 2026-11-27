-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_mk_eq_5310c7c00837
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:00.076587+00:00
-- url     : https://prove2.me/submissions/de43c7e1-4b8b-48e2-8bd1-4d82e42a12bd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eq_or_eq_conjugate_of_comp_eq_585524b3de8e
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
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
    (h : InfinitePlace.mk (φ.comp (algebraMap F E)) = InfinitePlace.mk (ψ.comp (algebraMap F E))) :
    ψ = φ ∨ ψ = ComplexEmbedding.conjugate φ := by
  refine eq_or_eq_conjugate_of_comp_eq F E φ ψ ?_
  rcases InfinitePlace.mk_eq_iff.1 h with h' | h'
  · exact h'
  · rw [← h']
    ext c
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
    exact (embedding_algebraMap_conj F E φ c).symm
end GroundTheory.Heights₂.Theta
