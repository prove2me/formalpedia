-- Prove2me | solution 1 for Sendov.one_le_lowJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:01.683478+00:00
-- url     : https://prove2.me/submissions/c871cb85-a49f-45db-b794-953133cd0724

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_continuous_lowX_pow
import Theorems.Thm_Sendov_prod_norm_le_lowX_pow
import Theorems.Thm_Sendov_continuous_prod_norm


set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ lowJ (n - 1) a := by
  refine hstar.trans ?_
  rw [lowJ]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    ((continuous_lowX_pow a (n - 1)).intervalIntegrable _ _) ?_
  intro u hu
  have h := prod_norm_le_lowX_pow ha0 ha1 hu.1 q hq1
  rwa [hqcard] at h
end Sendov
