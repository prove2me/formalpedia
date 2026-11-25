-- Prove2me | solution 1 for PI.LocDualGen.FpU.res_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:12.846261+00:00
-- url     : https://prove2.me/submissions/300440ea-44a2-4c95-94d2-869983e58e57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Theorems.Thm_PI_LocDualGen_FpU_res_iotaR
import Theorems.Thm_PI_LocDualGen_FpU_res_blift

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
    residue 𝒪[K] (Phi K l hcont c) = ∑ i, PadicInt.toZMod (c i) • bb K l i := by
  simp only [Phi, map_sum, map_mul, res_iotaR, res_blift, Algebra.smul_def]
end PI.LocDualGen.FpU
