-- Prove2me | solution 1 for PositivityTheory.Mix.bf_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:45.919012+00:00
-- url     : https://prove2.me/submissions/9fec0957-0c87-46c2-afbc-4ff9452a74e0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
namespace PositivityTheory.Mix
theorem _root_.solution (i j : Fin n) : bf c J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have e : (fun l => c ((Pi.single j 1 : Fin n → R) l)) = (Pi.single j 1 : Fin n → R) := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp
    · simp [Pi.single_apply, hl]
  simp only [bf, e, mulVec_single_one, single_one_dotProduct]
  rfl
end PositivityTheory.Mix
