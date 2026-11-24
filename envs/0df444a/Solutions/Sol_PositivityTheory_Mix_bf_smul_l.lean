-- Prove2me | solution 1 for PositivityTheory.Mix.bf_smul_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:34.826502+00:00
-- url     : https://prove2.me/submissions/9747ad02-b328-4b83-b2fa-dea3fce2c3dd

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
theorem _root_.solution (a : R) (u v) : bf c J (a • u) v = a * bf c J u v := by
  simp [bf, smul_dotProduct]
end PositivityTheory.Mix
