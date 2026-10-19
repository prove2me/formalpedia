-- Prove2me | solution 1 for SpherePacking.tendsto_scaled_log_factorial_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/894d6ac2-23a1-47ec-b950-e6767ebc461d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_factorialLogError
import Theorems.Thm_SpherePacking_scaled_log_factorial_identity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution
    (k : ℕ → ℕ) (u : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hu : u ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))
      atTop (nhds (u * Real.log u - u)) := by
  have herror :
      Tendsto (fun n : ℕ => factorialLogError (k n))
        atTop (nhds 0) :=
    tendsto_factorialLogError.comp hk
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((k n : ℝ) / (n : ℝ)))
        atTop (nhds (Real.log u)) :=
    (Real.continuousAt_log hu).tendsto.comp hratio
  have hproduct :=
    hratio.mul ((herror.add hlog).sub (tendsto_const_nhds (x := (1 : ℝ))))
  have heq :
      (fun n : ℕ =>
        ((k n : ℝ) / (n : ℝ)) *
          (factorialLogError (k n) +
            Real.log ((k n : ℝ) / (n : ℝ)) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) := by
    filter_upwards [hk.eventually (eventually_ne_atTop (0 : ℕ)),
      eventually_ne_atTop (0 : ℕ)] with n hkn hn
    exact (scaled_log_factorial_identity (k n) n hkn hn).symm
  simpa only [zero_add, mul_sub, mul_one] using hproduct.congr' heq
end SpherePacking
