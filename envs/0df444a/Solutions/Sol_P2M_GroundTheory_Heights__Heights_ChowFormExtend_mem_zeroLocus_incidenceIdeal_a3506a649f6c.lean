-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:24.725152+00:00
-- url     : https://prove2.me/submissions/be7c873a-52c3-4aaa-a42f-82b2e41886f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) (z : (Fin k × Fin n) ⊕ Fin n → E) :
    z ∈ zeroLocus E (incidenceIdeal I k) ↔
      (∀ g ∈ I, aeval (z ∘ Sum.inr) g = 0) ∧ ∀ i, ∑ j, z (Sum.inl (i, j)) * z (Sum.inr j) = 0 := by
  have key : z ∈ zeroLocus E (incidenceIdeal I k) ↔ incidenceIdeal I k ≤ vanishingIdeal F {z} :=
    ⟨fun h p hp => (mem_vanishingIdeal_singleton_iff z p).2 (h p hp),
      fun h p hp => (mem_vanishingIdeal_singleton_iff z p).1 (h hp)⟩
  rw [key, incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  refine and_congr ⟨fun h g hg => ?_, fun h g hg => ?_⟩ (forall_congr' fun i => ?_)
  · have := h hg
    rwa [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename] at this
  · rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]
    exact h g hg
  · rw [SetLike.mem_coe, mem_vanishingIdeal_singleton_iff]
    simp
end GroundTheory.Heights₂.Heights.ChowFormExtend
