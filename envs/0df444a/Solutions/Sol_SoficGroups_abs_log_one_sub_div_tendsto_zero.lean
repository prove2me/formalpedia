-- Prove2me | solution 1 for SoficGroups.abs_log_one_sub_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/93b0ed81-03da-4ade-954a-57236ce6d1e2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_abs_log_one_sub_le_two_mul

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (hH : ∀ n, 0 < H n)
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0))
    (hratio : Filter.Tendsto
      (fun n => eta n / H n) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => |Real.log (1 - eta n)| / H n)
      Filter.atTop (nhds 0) := by
  have hsmall : ∀ᶠ n in Filter.atTop,
      eta n < (1 : ℝ) / 2 :=
    heta.eventually (gt_mem_nhds (by norm_num))
  have hupper : ∀ᶠ n in Filter.atTop,
      |Real.log (1 - eta n)| / H n ≤
        2 * (eta n / H n) := by
    filter_upwards [hsmall] with n hn
    calc
      |Real.log (1 - eta n)| / H n ≤
          (2 * eta n) / H n :=
        (div_le_div_iff_of_pos_right (hH n)).2
          (abs_log_one_sub_le_two_mul
            (eta n) (heta0 n) hn.le)
      _ = 2 * (eta n / H n) := by ring
  have hlimit : Filter.Tendsto
      (fun n => 2 * (eta n / H n)) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul (2 : ℝ) hratio
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (hH n).le)
    hupper hlimit
end SoficGroups
