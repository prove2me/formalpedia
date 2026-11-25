-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:59.031804+00:00
-- url     : https://prove2.me/submissions/3da07f1d-b9a1-46f6-8ab0-652097e33152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (S : Finset Ω)
    (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ θ : Ω, IsIntegral F θ ∧ θ ∈ Algebra.adjoin F (S : Set Ω) ∧
      ∀ x ∈ IntermediateField.adjoin F (S : Set Ω), x ∈ Algebra.adjoin F {θ} := by
  haveI : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => hS x hx
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F (IntermediateField.adjoin F (S : Set Ω))
  have hθint : IsIntegral F (α : Ω) := (IsIntegral.of_finite F α).map (IntermediateField.adjoin F (S : Set Ω)).val
  have hK : IntermediateField.adjoin F {(α : Ω)} = IntermediateField.adjoin F (S : Set Ω) := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congr_arg IntermediateField.lift hα
  refine ⟨α, hθint, ?_, fun x hx => ?_⟩
  · have h1 : (α : Ω) ∈ IntermediateField.adjoin F (S : Set Ω) := α.2
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => (hS x hx).isAlgebraic)] at h1
    exact h1
  · rw [← hK, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hθint.isAlgebraic)] at hx
    exact hx
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
