-- Prove2me | solution 1 for PI.LocDualGen.FpU.Phi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:06.048315+00:00
-- url     : https://prove2.me/submissions/96fb301b-cae1-417a-bcfe-77536e6730f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO

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
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by
  simp only [Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
end PI.LocDualGen.FpU
