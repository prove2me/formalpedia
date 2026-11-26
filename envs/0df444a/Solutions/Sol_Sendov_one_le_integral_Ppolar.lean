-- Prove2me | solution 1 for Sendov.one_le_integral_Ppolar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:37.730795+00:00
-- url     : https://prove2.me/submissions/ebf90e2b-2d3b-4c74-9fb8-7dee5feed647

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_continuous_prod_norm
import Theorems.Thm_Sendov_prod_norm_le_Ppolar
import Theorems.Thm_Sendov_continuous_Ppolar
import Theorems.Thm_Sendov_continuous_rpow_const


set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine hstar.trans (intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    (((continuous_rpow_const he).comp (continuous_Ppolar a x)).intervalIntegrable _ _) ?_)
  intro u _
  exact prod_norm_le_Ppolar hn hqcard hq1 hx
end Sendov
