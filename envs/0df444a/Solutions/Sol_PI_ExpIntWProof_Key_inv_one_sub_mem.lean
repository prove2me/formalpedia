-- Prove2me | solution 1 for PI.ExpIntWProof.Key.inv_one_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:31.301126+00:00
-- url     : https://prove2.me/submissions/96b6db69-f88b-4624-ac6e-7f4537bcdc48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Theorems.Thm_PI_ExpIntWProof_Key_isClosed_Wp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.ExpIntWProof.Key
theorem _root_.solution {ξ : ℂ_[p]} (hξ : ξ ∈ Wp p) (h : ‖ξ‖ < 1) : (1 - ξ)⁻¹ ∈ Wp p := by
  have hs := (hasSum_geometric_of_norm_lt_one h).tendsto_sum_nat
  refine (isClosed_Wp p).mem_of_tendsto hs (Filter.Eventually.of_forall fun n => ?_)
  exact Subring.sum_mem _ fun i _ => Subring.pow_mem _ hξ i
end PI.ExpIntWProof.Key
