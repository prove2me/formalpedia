-- Prove2me | solution 1 for TunnellMap.Examples41.short_interval_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:06:41.698848+00:00
-- url     : https://prove2.me/submissions/b2e03e9d-8e81-453d-8e34-91b0dc5fbbf2

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    qForm ⟨1, -4, 1⟩ = 20 ∧
      qBilinear (residualSourceLift s2) ⟨1, -4, 1⟩ = 20 ∧
      M 41 20 1 = 420 ∧
      Int.sqrt 420 = 20 ∧
      bLower 41 frame41 20 1 = -4 ∧
      bUpper 41 frame41 20 1 = -4 ∧
      frame41.halfDiscriminant 20 1 (-4) = 4 := by
  norm_num [qForm, qBilinear, s2, midpointSource, residualSourceLift, bLift,
    M, bLower, bUpper, alpha, beta, delta, epsilon, K, frame41,
    OrthogonalFrame.halfDiscriminant, dot]
end TunnellMap.Examples41
