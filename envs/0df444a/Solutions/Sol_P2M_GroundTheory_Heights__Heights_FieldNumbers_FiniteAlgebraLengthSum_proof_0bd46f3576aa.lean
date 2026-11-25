-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FiniteAlgebraLengthSum_proof_0bd46f3576aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:40.864565+00:00
-- url     : https://prove2.me/submissions/49c41c5b-a8a4-43b4-a6f9-cfa105cba898

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFiniteAlgebraLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LengthSumLocalizations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFiniteAlgebraLengthSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LengthSumLocalizations_length_eq_sum_b684c5e7ef89


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Module
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace FiniteAlgebraLengthSum
theorem _root_.solution : FiniteAlgebraLengthSum.Statement := by
  classical
  intro A B _ _ _ _ _ ι _ 𝔪 h𝔪 hinj hall C _ _ hC α
  have : ∀ i, (𝔪 i).IsMaximal := h𝔪
  have : ∀ i, IsLocalization.AtPrime (C i) (𝔪 i) := hC
  have hrange : LinearMap.range (LinearMap.lsmul A B α) =
      (Ideal.span {algebraMap A B α}).restrictScalars A := by
    ext b
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ hrange).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B α})).length_eq,
    LengthSumLocalizations.length_eq_sum 𝔪 C hinj hall A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ring.ord, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i)
    (Ideal.span {algebraMap A B α})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]
end FiniteAlgebraLengthSum
end GroundTheory.Heights₂.Heights.FieldNumbers
