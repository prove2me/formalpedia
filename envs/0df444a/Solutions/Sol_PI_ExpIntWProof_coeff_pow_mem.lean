-- Prove2me | solution 1 for PI.ExpIntWProof.coeff_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:18.150622+00:00
-- url     : https://prove2.me/submissions/d4150539-0560-4eea-93ce-5df88c6f1fb0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Theorems.Thm_PI_ExpIntWProof_mem_Wf

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
theorem _root_.solution {σ : Type} (p : ℕ) [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p])
    (hf : CoefWf f) : ∀ n : ℕ, ∀ α, MvPowerSeries.coeff α (f ^ n) ∈ Wf p := by
  classical
  intro n
  induction n with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs
    · exact (Wf p).one_mem
    · exact (Wf p).zero_mem
  | succ n ih =>
    intro α
    rw [pow_succ, MvPowerSeries.coeff_mul]
    exact (Wf p).sum_mem fun x _ => (Wf p).mul_mem (ih x.1) (mem_Wf.mpr (hf x.2))
end PI.ExpIntWProof
