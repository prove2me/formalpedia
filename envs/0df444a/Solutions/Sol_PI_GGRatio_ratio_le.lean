-- Prove2me | solution 1 for PI.GGRatio.ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:41.480575+00:00
-- url     : https://prove2.me/submissions/95fd521a-f8ab-4dbd-9431-67ad63e82a5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
import Theorems.Thm_PI_GGRatio_pow_gauss_eq_prod
import Theorems.Thm_PI_GGRatio_inv_one_sub_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset
namespace PI.GGRatio
theorem _root_.solution (q k d : ℕ) (hq : 2 ≤ q) (hd : ∏ i ∈ Ico 1 k, (q ^ i - 1) ≤ d) :
    ((q ^ (k * (k - 1) / 2) : ℕ) : ℝ) / (d : ℝ) ≤ ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hcast : ((∏ i ∈ Ico 1 k, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub h1]
    ring
  have hprodpos : (0 : ℝ) < ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have h2 := one_lt_pow₀ hq1 (by omega : i ≠ 0)
    linarith
  have hdle : ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) ≤ d := by
    rw [← hcast]
    exact_mod_cast hd
  have e : ∏ i ∈ Ico 1 k, (1 - ((q : ℝ) ^ i)⁻¹)⁻¹ = (q : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Ico 1 k, ((q : ℝ) ^ i - 1) := by
    rw [pow_gauss_eq_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have h1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    exact inv_one_sub_inv _ (one_lt_pow₀ hq1 (by omega))
  rw [e]
  push_cast
  exact div_le_div_of_nonneg_left (by positivity) hprodpos hdle
end PI.GGRatio
