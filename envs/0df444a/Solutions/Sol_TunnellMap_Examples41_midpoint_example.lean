-- Prove2me | solution 1 for TunnellMap.Examples41.midpoint_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:37:06.364282+00:00
-- url     : https://prove2.me/submissions/fb8b0b0c-12b6-46ca-b7d9-502455403639

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    bLift midpointSource = ⟨-2, -5, 2⟩ ∧
      aLift midpointTarget = ⟨4, -3, 0⟩ ∧
      IsHalfSum ⟨1, -4, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      IsHalfDiff ⟨-3, -1, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      qForm ⟨1, -4, 1⟩ = 20 ∧
      qForm ⟨3, 1, -1⟩ = 21 ∧
      qBilinear ⟨-2, -5, 2⟩ ⟨1, -4, 1⟩ = 20 ∧
      vadd (negTriple ⟨-2, -5, 2⟩) (vsmul 2 ⟨1, -4, 1⟩) =
        ⟨4, -3, 0⟩ := by
  norm_num [midpointSource, midpointTarget, bLift, aLift, IsHalfSum, IsHalfDiff,
    qForm, qBilinear, vadd, vsmul, negTriple]
end TunnellMap.Examples41
