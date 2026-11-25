-- Prove2me | solution 1 for PI.LocDualGen.FpU.trace_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:01:03.301567+00:00
-- url     : https://prove2.me/submissions/51f4e60c-edcb-4a4d-9adf-e405555690ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
import Theorems.Thm_PI_LocDualGen_FpU_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes
namespace PI.LocDualGen.FpU
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : ‖Algebra.trace ℚ_[l] K (x : K)‖ ≤ 1 := by
  rw [trace_eq K l hcont huni]
  exact (∑ i, coef K l hcont huni (x * blift K l i) i).2
end PI.LocDualGen.FpU
