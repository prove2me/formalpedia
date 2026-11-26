-- Prove2me | solution 1 for Sendov.low_degree_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:44.925026+00:00
-- url     : https://prove2.me/submissions/c5a77261-8c33-4cc0-921d-7b0065b01bf6

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_one_le_lowJ
import Theorems.Thm_Sendov_lowJ_lt_one

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    False := by
  have h1 := one_le_lowJ (n := n) (le_of_lt ha0) (le_of_lt ha1) hqcard hq1 hstar
  have h2 := lowJ_lt_one ha0 ha1 (m := n - 1) (by omega) (by omega)
  linarith
end Sendov
