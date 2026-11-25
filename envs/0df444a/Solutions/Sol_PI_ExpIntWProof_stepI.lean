-- Prove2me | solution 1 for PI.ExpIntWProof.stepI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:00.858307+00:00
-- url     : https://prove2.me/submissions/0d3f96ed-60e3-469e-8108-516d83d49a53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Theorems.Thm_PI_ExpIntWProof_mem_Wf
import Theorems.Thm_PI_ExpIntWProof_inv_nat_mem_Wf
import Theorems.Thm_PI_ExpIntWProof_coeff_pow_mem

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
theorem _root_.solution : StepI := by
  intro p _ σ f hf n
  rw [← mem_Wf]
  show (∑ k ∈ Finset.range _, MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p])) ∈ Wf p
  refine (Wf p).sum_mem fun k _ => ?_
  rw [div_eq_mul_inv]
  exact (Wf p).mul_mem (coeff_pow_mem p f hf k n) (inv_nat_mem_Wf p _ (Nat.factorial_ne_zero k))
end PI.ExpIntWProof
