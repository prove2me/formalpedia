-- Prove2me | solution 1 for Sendov.prod_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:44.937979+00:00
-- url     : https://prove2.me/submissions/8cf28be6-3294-4e98-8662-48a7e33102ac

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect
import Theorems.Thm_Sendov_prod_norm_nonneg

set_option autoImplicit false
open Sendov
open Multiset
namespace Sendov
theorem _root_.solution : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    simp only [Multiset.map_cons, Multiset.prod_cons]
    nlinarith [norm_nonneg w]
end Sendov
