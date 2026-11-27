-- Prove2me | solution 1 for UpperTheory.V.U3.hasSimilitudeFactor_diagonalRepr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:03.9051+00:00
-- url     : https://prove2.me/submissions/44cbb244-a79f-4491-935b-0c92609c74dc

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne

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
namespace UpperTheory.V.U3
theorem _root_.solution {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) :
    HasMult η (r0 η Ψ) := fun _ => rfl
end UpperTheory.V.U3
