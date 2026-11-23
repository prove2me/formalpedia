-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:55.824805+00:00
-- url     : https://prove2.me/submissions/b9f02a51-8a3f-43f5-9f9e-cf453e05556d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  ext α
  rw [coeff_expMv, Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    rw [zero_pow hn, map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
