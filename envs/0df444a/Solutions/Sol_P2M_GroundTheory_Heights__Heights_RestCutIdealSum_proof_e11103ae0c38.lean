-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutIdealSum_proof_e11103ae0c38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:18.744208+00:00
-- url     : https://prove2.me/submissions/06bb1357-396f-461e-bbed-0f5d8a9964ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIdealSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutIdealSum
theorem _root_.solution : RestCutIdealSum.Statement := by
  intro f N A hA
  rw [restPsumIdeal, restPsumIdeal_generators_eq_range, Ideal.mem_span_range_iff_exists_fun] at hA
  obtain ⟨c, hc⟩ := hA
  exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
end RestCutIdealSum
end GroundTheory.Heights₂.Heights
