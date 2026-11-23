-- Prove2me | solution 1 for UpperTheory.V.U3.unitaryThreeReflection_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:47.289729+00:00
-- url     : https://prove2.me/submissions/9eb05a2f-1f5a-4dcd-9889-2c12580487d1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.U3
open Matrix
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G]
namespace UpperTheory.V.U3
theorem _root_.solution (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) : (r0 η Ψ g).left = tor R (Ψ g) := rfl
end UpperTheory.V.U3
