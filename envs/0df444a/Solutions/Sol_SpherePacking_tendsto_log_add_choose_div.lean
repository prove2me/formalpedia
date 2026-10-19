-- Prove2me | solution 1 for SpherePacking.tendsto_log_add_choose_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/b25f8e54-1eb5-4ecf-8342-77bb1f6afcd4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_scaled_log_factorial_sub
import Theorems.Thm_SpherePacking_log_add_choose_div_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution
    (k l : ℕ → ℕ) (u v : ℝ)
    (hk : Tendsto k atTop atTop)
    (hl : Tendsto l atTop atTop)
    (hku : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hlv : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ))
      atTop (nhds v))
    (hu : 0 < u) (hv : 0 < v) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ))
      atTop
      (nhds ((u + v) * Real.log (u + v) -
        u * Real.log u - v * Real.log v)) := by
  have hsum : Tendsto (fun n : ℕ => k n + l n) atTop atTop := by
    apply tendsto_atTop_mono (f := k)
    · intro n
      omega
    · exact hk
  have hsumratio :
      Tendsto (fun n : ℕ => ((k n + l n : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (u + v)) := by
    simpa only [Nat.cast_add, add_div] using hku.add hlv
  have htotal :=
    tendsto_scaled_log_factorial_sub (fun n => k n + l n)
      (u + v) hsum hsumratio (ne_of_gt (add_pos hu hv))
  have hfirst := tendsto_scaled_log_factorial_sub k u hk hku hu.ne'
  have hsecond := tendsto_scaled_log_factorial_sub l v hl hlv hv.ne'
  have hcomb := (htotal.sub hfirst).sub hsecond
  have heq :
      (fun n : ℕ =>
        (Real.log ((k n + l n).factorial : ℝ) / (n : ℝ) -
          (((k n + l n : ℕ) : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((k n).factorial : ℝ) / (n : ℝ) -
            ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((l n).factorial : ℝ) / (n : ℝ) -
            ((l n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))) =ᶠ[atTop]
  (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change _ = Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)
    rw [log_add_choose_div_eq]
    push_cast
    ring
  have hlimit :
      ((u + v) * Real.log (u + v) - (u + v)) -
          (u * Real.log u - u) - (v * Real.log v - v) =
        (u + v) * Real.log (u + v) -
          u * Real.log u - v * Real.log v := by
    ring
  rw [← hlimit]
  exact hcomb.congr' heq
end SpherePacking
