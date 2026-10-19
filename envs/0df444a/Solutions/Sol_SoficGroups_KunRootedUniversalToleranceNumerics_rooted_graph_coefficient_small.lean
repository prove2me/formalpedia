-- Prove2me | solution 1 for SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_coefficient_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/209db7b2-94a3-410a-8f96-5933e5a1faf0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedUniversalToleranceNumerics
namespace SoficGroups.KunRootedUniversalToleranceNumerics
theorem _root_.solution
    {d q : ℝ} (hd : 0 < d) (hq : q < 1) :
    0 < d * (1 - q) ^ 2 / 288 ∧
      216 * (d * (1 - q) ^ 2 / 288) < d * (1 - q) ^ 2 := by
  have hgap : 0 < d * (1 - q) ^ 2 := by
    positivity
  constructor
  · positivity
  · nlinarith
end SoficGroups.KunRootedUniversalToleranceNumerics
