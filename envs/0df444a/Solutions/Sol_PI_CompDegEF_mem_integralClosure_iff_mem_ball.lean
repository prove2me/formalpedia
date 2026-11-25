-- Prove2me | solution 1 for PI.CompDegEF.mem_integralClosure_iff_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:28.08882+00:00
-- url     : https://prove2.me/submissions/02f0adb4-e2e6-46f9-95d5-d83cd92284bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
import Theorems.Thm_PI_CompDegEF_norm_le_one_iff_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.CompDegEF
theorem _root_.solution (K : FinExt l) (x : ↥K.1) :
    x ∈ integralClosure ℤ_[l] ↥K.1 ↔ x ∈ ball K := by
  rw [mem_integralClosure_iff]
  show IsIntegral ℤ_[l] x ↔ ‖((x : ↥K.1) : Om l)‖ ≤ 1
  rw [norm_le_one_iff_isIntegral]
  first
    | exact (isIntegral_algebraMap_iff (A := ↥K.1) (B := Om l) (algebraMap (↥K.1) (Om l)).injective).symm
    | exact (isIntegral_algHom_iff ((K.1.val).restrictScalars ℤ_[l]) K.1.val.injective).symm
end PI.CompDegEF
