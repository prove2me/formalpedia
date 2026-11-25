-- Prove2me | solution 1 for PI.ExpIntWProof.inv_nat_mem_Wf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:36.900698+00:00
-- url     : https://prove2.me/submissions/76b42f31-5270-41bb-b2f2-59cdf799f20d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Theorems.Thm_PI_ExpIntWProof_mem_Wf
import Theorems.Thm_PI_ExpIntWProof_inv_natCast_mem_wittIntegers


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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    ((m : ℂ_[p]))⁻¹ ∈ Wf p := by
  rw [mem_Wf]
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  refine ⟨k, ?_⟩
  have hpk : (p : ℂ_[p]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hpk, one_mul]
  exact inv_natCast_mem_wittIntegers p u hu
end PI.ExpIntWProof
