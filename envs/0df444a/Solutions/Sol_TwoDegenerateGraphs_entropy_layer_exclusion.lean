-- Prove2me | solution 1 for TwoDegenerateGraphs.entropy_layer_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/98fcc8df-07e0-44e7-b055-fc7068d76c06

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_entropy_potential_increment
import Theorems.Thm_TwoDegenerateGraphs_entropy_potential_layers_impossible

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (depth : ℕ) (potential conditionalEntropy error : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (herror : ∀ i < depth, error i < entropySlack)
    (hlower : ∀ i < depth,
      midpointBeta - entropySlack < conditionalEntropy i)
    (hupper : ∀ i < depth,
      conditionalEntropy i ≤
        entropyLowerEndpoint +
          (potential (i + 1) - potential i) / 2 + error i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  apply entropy_potential_layers_impossible depth potential hrange
    (hdepth := hdepth)
  intro i hi
  exact entropy_potential_increment (potential i) (potential (i + 1))
    (conditionalEntropy i) (error i)
    (herror i hi) (hlower i hi) (hupper i hi)
end TwoDegenerateGraphs
