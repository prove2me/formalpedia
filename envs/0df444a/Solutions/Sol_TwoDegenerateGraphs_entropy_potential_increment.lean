-- Prove2me | solution 1 for TwoDegenerateGraphs.entropy_potential_increment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/49c45453-7da6-47fd-88c7-94b874b7c821

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < entropySlack)
    (hlower : midpointBeta - entropySlack < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpoint +
        (potentialAfter - potentialBefore) / 2 + error) :
    certifiedWindowWidth / 2 < potentialAfter - potentialBefore := by
  have hwindow := entropyWindow_eq_certifiedWindowWidth
  unfold midpointBeta entropySlack at hlower
  unfold entropySlack at herror
  linarith
end TwoDegenerateGraphs
