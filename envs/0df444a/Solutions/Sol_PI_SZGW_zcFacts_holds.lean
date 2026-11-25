-- Prove2me | solution 1 for PI.SZGW.zcFacts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:14.643448+00:00
-- url     : https://prove2.me/submissions/928fb8b3-c26a-4f60-8a32-7d8b04bef98f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero
import Theorems.Thm_PI_SZGW_isUnit_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.SZGW
open PI.BeDiagZp.ContPf
namespace PI.SZGW
theorem _root_.solution : ZcFacts := by
  intro p _ h2
  refine ⟨?_, ?_, ?_, ?_, ?_, isUnit_two h2⟩
  · intro a b; simp [PI.BeDiagZp.zc]
  · intro a b; simp [PI.BeDiagZp.zc]
  · simp [PI.BeDiagZp.zc]
  · simp [PI.BeDiagZp.zc]
  · simp only [PI.BeDiagZp.zc]
    have e : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by norm_cast
    rw [e, map_ofNat]
end PI.SZGW
