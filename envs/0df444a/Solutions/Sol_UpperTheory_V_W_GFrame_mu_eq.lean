-- Prove2me | solution 1 for UpperTheory.V.W.GFrame.mu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:44.043133+00:00
-- url     : https://prove2.me/submissions/98947070-9a10-45b7-8c39-47b7aa9cbcf6

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing UpperTheory.V.Alg
open UpperTheory UpperTheory.V UpperTheory.V.W
attribute [instance] DetObj.ring DetObj.alg DetObj.co
variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (r : Resid F O n)
namespace UpperTheory.V.W
namespace GFrame
theorem _root_.solution (v : F.Vl) : F.mu v = muG l (F.Gv v) := rfl
end GFrame
end UpperTheory.V.W
