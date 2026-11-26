-- Prove2me | solution 1 for TunnellMap.Examples41.lattice_frame_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:07.984137+00:00
-- url     : https://prove2.me/submissions/c27ec520-9c57-4411-911b-439cf3a678ce

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    tau (residualSourceLift s2) = ⟨0, -5, -4⟩ ∧
      frame41.e₁ = ⟨1, 0, 0⟩ ∧
      frame41.e₂ = ⟨0, -4, 5⟩ ∧
      frame41.z = ⟨0, -1, 1⟩ ∧
      cross frame41.e₁ frame41.e₂ = tau (residualSourceLift s2) ∧
      dot (tau (residualSourceLift s2)) frame41.z = 1 := by
  norm_num [frame41, s2, midpointSource, residualSourceLift, bLift, tau, cross, dot]
end TunnellMap.Examples41
