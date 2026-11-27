-- Prove2me | solution 1 for PIW.ENSpec.ev_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:46.127272+00:00
-- url     : https://prove2.me/submissions/93f5b2a2-bcea-4ea1-8ecd-732b9cbd3a99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PIW PIW.ENSpec
open PI.EagonNorthcott MvPolynomial RingTheory.Sequence
variable {R : Type u} [CommRing R] {D : ℕ} (x : Fin D → R)
namespace PIW.ENSpec
theorem _root_.solution (c : Fin D → ℤ) : eval x (lin (X : Fin D → MvPolynomial (Fin D) R) c) = lin x c := by
  simp [lin]
end PIW.ENSpec
