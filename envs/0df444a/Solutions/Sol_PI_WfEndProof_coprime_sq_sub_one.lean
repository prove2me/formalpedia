-- Prove2me | solution 1 for PI.WfEndProof.coprime_sq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:15.722878+00:00
-- url     : https://prove2.me/submissions/1fa38d0b-78ee-46fd-883d-c3d40fa79f5e

import Definitions.Def_Formalism_PeriodIntegrals_W2pair
import Definitions.Def_Formalism_PeriodIntegrals_WfRing
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_FlogConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfEndProof
open PI
namespace PI.WfEndProof
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] : Nat.Coprime (p ^ 2 - 1) p := by
  have hp' := hp.out
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp').2 ?_)
  intro h
  have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h3 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h
  have h4 : p ^ 2 - (p ^ 2 - 1) = 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp'.pos
    omega
  rw [h4] at h3
  exact hp'.one_lt.ne' (Nat.dvd_one.1 h3)
end PI.WfEndProof
