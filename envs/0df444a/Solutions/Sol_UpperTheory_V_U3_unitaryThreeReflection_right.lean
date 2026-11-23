-- Prove2me | solution 1 for UpperTheory.V.U3.unitaryThreeReflection_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:05.433163+00:00
-- url     : https://prove2.me/submissions/115486a7-ee7d-40c1-8031-b2f86ea97c19

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
theorem _root_.solution (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) : (r0 η Ψ g).right = η g := rfl
end UpperTheory.V.U3
