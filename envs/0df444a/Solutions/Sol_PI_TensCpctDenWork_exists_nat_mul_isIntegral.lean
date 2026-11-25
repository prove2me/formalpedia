-- Prove2me | solution 1 for PI.TensCpctDenWork.exists_nat_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:44.046699+00:00
-- url     : https://prove2.me/submissions/4c95392f-68fd-491b-8650-1b98136e7f55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TensCpctDenWork
open NumberField IsDedekindDomain TensorProduct
namespace PI.TensCpctDenWork
theorem _root_.solution {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ D : ℕ, 0 < D ∧ IsIntegral ℤ ((D : E) * x) := by
  obtain ⟨n, hn, -, hi⟩ := NumberField.exists_nat_le_mulHeight₁ x
  exact ⟨n, Nat.pos_of_ne_zero hn, hi⟩
end PI.TensCpctDenWork
