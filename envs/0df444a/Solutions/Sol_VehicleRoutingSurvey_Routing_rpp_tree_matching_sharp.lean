-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.rpp_tree_matching_sharp
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T14:41:32.965795+00:00
-- url     : https://prove2.me/submissions/814c729d-9e44-4354-87e9-d42a2207390f

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Theorems.Thm_VehicleRoutingSurvey_Routing_rpp_tree_matching_runtime

open VehicleRoutingSurvey.Routing in
theorem solution :
    (∀ I : Service, Rural I →
      (∃ u ts, RuralRun I u ts) ∧
      (∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I) ∧
      (∀ u ts, RuralRun I u ts → Feasible I u ts ∧
        pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
        Rural I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ RuralRun I u ts ∧
        (3 / 2 - ε) * optimum I < pathCost I.graph ts) ∧
    (∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N) := 
  rpp_tree_matching_sharp_of_implementation rpp_tree_matching_runtime
