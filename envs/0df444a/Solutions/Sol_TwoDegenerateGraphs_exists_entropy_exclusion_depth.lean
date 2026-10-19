-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_entropy_exclusion_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/a13bc10b-dd81-4eb8-8dcc-6e45fd06ee7b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∃ depth : ℕ, 0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) := by
  obtain ⟨depth, hdepth⟩ :=
    exists_nat_gt ((2 : ℝ) / certifiedWindowWidth)
  have hwidth := certifiedWindowWidth_pos
  have hdepth_real : 0 < (depth : ℝ) :=
    (div_pos (by norm_num) hwidth).trans hdepth
  have hdepth_nat : 0 < depth := by exact_mod_cast hdepth_real
  refine ⟨depth, hdepth_nat, ?_⟩
  have hproduct := (div_lt_iff₀ hwidth).mp hdepth
  nlinarith
end TwoDegenerateGraphs
