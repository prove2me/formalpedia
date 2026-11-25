-- Prove2me | solution 1 for PI.ExpIntWProof.inv_mem_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:15.662645+00:00
-- url     : https://prove2.me/submissions/699ed4dc-4797-4f9e-80fb-80d883c15ab9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (p : ℕ) [Fact p.Prime] {x : ℂ_[p]} (hx : x ∈ Wp p)
    (h : ‖1 - x‖ < 1) : x⁻¹ ∈ Wp p := by
  have hs : HasSum (fun n : ℕ => (1 - x) ^ n) (1 - (1 - x))⁻¹ := hasSum_geometric_of_norm_lt_one h
  rw [sub_sub_cancel] at hs
  have hcl : IsClosed (Wp p : Set ℂ_[p]) := Subring.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
  exact Subring.sum_mem _ fun i _ => pow_mem (sub_mem (one_mem _) hx) i
end PI.ExpIntWProof
