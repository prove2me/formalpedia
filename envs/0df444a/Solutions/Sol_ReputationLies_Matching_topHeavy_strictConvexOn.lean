-- Prove2me | solution 1 for ReputationLies.Matching.topHeavy_strictConvexOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:34:10.671035+00:00
-- url     : https://prove2.me/submissions/4632262a-2280-4580-8565-fd95d317b79f

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

open ReputationLies.Matching in
theorem solution (P : Primitives) (hP : P.Standing) :
    (P.TopHeavy → StrictConvexOn ℝ (Icc 0 1) P.F) ∧
    (P.BottomHeavy → StrictConcaveOn ℝ (Icc 0 1) P.F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hF⟩ := hP
  have hc : ContinuousOn P.F (Icc 0 1) := hF.continuousOn
  constructor
  · intro hT
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1) hc
    rw [interior_Icc]
    exact hT
  · intro hB
    apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1) hc
    rw [interior_Icc]
    exact hB
