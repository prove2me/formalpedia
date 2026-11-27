-- Prove2me | solution 1 for PI.RamBoundW.apL_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:28.828994+00:00
-- url     : https://prove2.me/submissions/0ce0d7de-20f3-4460-a86c-d5c0522395de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationBound_AlgebraMapMemFil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.RamBoundW
variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*} (δ : ι → Derivation R P P)
namespace PI.RamBoundW
theorem _root_.solution (i : ι) (T : List ι) (M : P) : apL δ (i :: T) M = apL δ T (δ i M) := rfl
end PI.RamBoundW
