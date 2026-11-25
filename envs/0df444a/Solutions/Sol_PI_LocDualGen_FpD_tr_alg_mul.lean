-- Prove2me | solution 1 for PI.LocDualGen.FpD.tr_alg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:57.691345+00:00
-- url     : https://prove2.me/submissions/51706789-682f-4880-89dd-1a59c06a4e82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
namespace PI.LocDualGen.FpD
theorem _root_.solution (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
end PI.LocDualGen.FpD
