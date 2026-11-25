-- Prove2me | solution 1 for PI.VolStabW.LocalCountingSum.sum_cnt_bigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:15.122009+00:00
-- url     : https://prove2.me/submissions/bb642a12-1a31-4068-a746-1e931ce5eeaf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
import Theorems.Thm_PI_VolStabW_LocalCountingSum_sum_cnt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
open PI.VolStabW.LocalCountingSum
variable (K : Type) [Field K] [NumberField K]
namespace PI.VolStabW.LocalCountingSum
theorem _root_.solution :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp only [sum_cnt, Real.rpow_one]
  have ht := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.cast_le] at ht
  refine isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
    (g := fun n : ℕ ↦ (n : ℝ)) ?_ _ ht
  filter_upwards [eventually_ne_atTop 0] with n hn h
  exact absurd h (by exact_mod_cast hn)
end PI.VolStabW.LocalCountingSum
