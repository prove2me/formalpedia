-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:31.043734+00:00
-- url     : https://prove2.me/submissions/ce022c7e-2f99-4956-91f8-20929ce23f07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_of_isMultiHomogIdeal__19cf94e31a60

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SupSpanMultiHomog
theorem _root_.solution : SupSpanMultiHomog.Statement := by
  classical
  intro R _ K _ ι I x e hI hx
  have h1 := isHomogeneous_of_isMultiHomogIdeal' hI
  have h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  have h := h1.sup h2
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b
end SupSpanMultiHomog
end GroundTheory.Heights₂.Heights.NumbersDVR
