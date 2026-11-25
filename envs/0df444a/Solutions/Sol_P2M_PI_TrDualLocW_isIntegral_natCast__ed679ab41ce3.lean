-- Prove2me | solution 1 for P2M_PI_TrDualLocW_isIntegral_natCast__ed679ab41ce3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:51.426267+00:00
-- url     : https://prove2.me/submissions/5afe047e-a3f3-447c-98b2-55e0cf74d422

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
namespace PI.TrDualLocW
theorem _root_.solution (n : ℕ) : IsIntegral ℤ (n : K) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ))
end PI.TrDualLocW
