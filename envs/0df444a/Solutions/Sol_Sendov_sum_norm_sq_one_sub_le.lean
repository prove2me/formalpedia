-- Prove2me | solution 1 for Sendov.sum_norm_sq_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:20.000277+00:00
-- url     : https://prove2.me/submissions/3159a48c-471e-4ba7-854f-fc48d36ad34f

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sum_norm_sq_one_sub_split
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_sum_norm_sq_le_card
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub hn]
    ring
  have hcast : ∀ v : ℂ, 1 - (a : ℂ) * (t : ℂ) * v = 1 + ((-(a * t) : ℝ) : ℂ) * v := by
    intro v
    push_cast
    ring
  simp only [hcast]
  rw [sum_norm_sq_one_sub_split, hx, hNcast]
  have hsum2 := sum_norm_sq_le_card q hq1
  rw [hNcast] at hsum2
  simp only [QQ]
  nlinarith [hsum2, sq_nonneg (a * t)]
end Sendov
