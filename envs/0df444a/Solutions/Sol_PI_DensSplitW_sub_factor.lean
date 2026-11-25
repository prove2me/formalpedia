-- Prove2me | solution 1 for PI.DensSplitW.sub_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:10.888471+00:00
-- url     : https://prove2.me/submissions/74f6ebc1-835d-4f23-b9e4-70afdf948638

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution (q N i : ℕ) (hq : 0 < q) (hi : i ≤ N) :
    ((q ^ N - q ^ i : ℕ) : ℝ) = (q : ℝ) ^ N * (1 - ((q : ℝ) ^ (N - i))⁻¹) := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi), Nat.cast_pow, Nat.cast_pow]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h : (q : ℝ) ^ N = (q : ℝ) ^ i * (q : ℝ) ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hne : (q : ℝ) ^ (N - i) ≠ 0 := by positivity
  rw [h]
  field_simp
end PI.DensSplitW
