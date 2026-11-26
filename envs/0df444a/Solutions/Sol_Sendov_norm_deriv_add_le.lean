-- Prove2me | solution 1 for Sendov.norm_deriv_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:20.897342+00:00
-- url     : https://prove2.me/submissions/7369b861-2d96-4300-9cab-dbefdbe242fd

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdMap_norm_le
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_norm_sumEraseProdC_le
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProdC_id_eq
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.Fprod_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a x y t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (ha0 : 0 ≤ a) (ht0 : 0 ≤ t)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = (((n : ℝ) - 1) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
        + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
      ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set S : ℂ := sumEraseProdC q (fun v => v ^ 2) (fun v => 1 - (a : ℂ) * (t : ℂ) * v) with hS
  have hmain : (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
      + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t
      = -((a : ℂ) ^ 2 * (t : ℂ)) * S := by
    rw [sumEraseProdC_id_eq, hsum, ← hS]
    ring
  rw [hmain, norm_mul]
  have hnorm : ‖-((a : ℂ) ^ 2 * (t : ℂ))‖ = a ^ 2 * t := by
    simp [abs_of_nonneg ha0, abs_of_nonneg ht0]
  rw [hnorm]
  have hSle : ‖S‖ ≤ sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖) := by
    rw [hS]
    refine norm_sumEraseProdC_le _ _ q ?_
    intro v hv
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg v) (hq1 v hv)
  have hbd := sumEraseProdMap_norm_le (a := a) (x := x) (t := t) hn hqcard hq0 hq1 hx
  have hfac : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg (pow_nonneg ha0 2) ht0
  calc a ^ 2 * t * ‖S‖
      ≤ a ^ 2 * t * (((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
        mul_le_mul_of_nonneg_left (hSle.trans hbd) hfac
    _ = a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by ring
end Sendov
