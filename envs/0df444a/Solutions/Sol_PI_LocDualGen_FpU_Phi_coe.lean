-- Prove2me | solution 1 for PI.LocDualGen.FpU.Phi_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:36.064547+00:00
-- url     : https://prove2.me/submissions/005b5842-9e8a-4424-9020-f7f666f80533

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Theorems.Thm_PI_LocDualGen_FpU_iotaR_coe

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
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by
  unfold Phi
  push_cast
  simp only [iotaR_coe]
end PI.LocDualGen.FpU
