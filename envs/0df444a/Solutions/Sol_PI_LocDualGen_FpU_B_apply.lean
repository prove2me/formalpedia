-- Prove2me | solution 1 for PI.LocDualGen.FpU.B_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:58.346485+00:00
-- url     : https://prove2.me/submissions/e870e188-bd34-41d3-a4e0-7c7a1ff46a87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator

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
    (i : Fin (fdim K l)) : B K l hcont huni i = (blift K l i : K) := by
  simp [B]
end PI.LocDualGen.FpU
