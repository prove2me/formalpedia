-- Prove2me | solution 1 for Sendov.prod_norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:49:57.100206+00:00
-- url     : https://prove2.me/submissions/9d67a047-5b20-4875-a033-e58f768d9d42

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect

set_option autoImplicit false
open Sendov
open Multiset
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) : 0 ≤ (s.map (fun z => ‖z‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg z
end Sendov
