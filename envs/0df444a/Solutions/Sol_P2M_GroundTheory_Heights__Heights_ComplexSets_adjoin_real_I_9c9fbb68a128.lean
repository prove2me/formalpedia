-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_adjoin_real_I_9c9fbb68a128
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:10.965792+00:00
-- url     : https://prove2.me/submissions/53776bd8-0828-44c4-9b67-a9a782a49b87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : IntermediateField.adjoin ℝ {Complex.I} = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [← Complex.re_add_im z]
  have hI := IntermediateField.mem_adjoin_simple_self ℝ Complex.I
  have hre : (z.re : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.re
  have him : (z.im : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.im
  exact add_mem hre (mul_mem him hI)
end GroundTheory.Heights₂.Heights.ComplexSets
