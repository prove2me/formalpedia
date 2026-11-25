-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealMultiHomog_proof_41306882bd1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:49.757874+00:00
-- url     : https://prove2.me/submissions/79b5ea02-2252-4277-a37c-b1bb9b167e23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isWeightedHomogeneous_map_of_2de25fb32301
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_span_forms_of_isMultiHomogIdeal_934319068e0f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpecialIdealMultiHomog
theorem _root_.solution : SpecialIdealMultiHomog.Statement := by
  classical
  intro O _ _ _ K _ ι P hP
  have hspan : specialIdeal P = Ideal.span
      (MvPolynomial.map (IsLocalRing.residue O) ''
        {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b}) := by
    rw [specialIdeal, ← Ideal.map_span, span_forms_of_isMultiHomogIdeal hP]
  have hhom : (specialIdeal P).IsHomogeneous
      (weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι)) := by
    rw [hspan]
    apply Ideal.homogeneous_span
    rintro _ ⟨f, ⟨_, b, hb⟩, rfl⟩
    exact ⟨b, (mem_weightedHomogeneousSubmodule _ _ _ _).2
      (isWeightedHomogeneous_map_of _ _ hb)⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem _ _ hhom hf b
end SpecialIdealMultiHomog
end GroundTheory.Heights₂.Heights.NumbersDVR
