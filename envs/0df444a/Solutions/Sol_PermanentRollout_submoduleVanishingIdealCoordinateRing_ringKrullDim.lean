-- Prove2me | solution 1 for PermanentRollout.submoduleVanishingIdealCoordinateRing_ringKrullDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/91d8b378-d7bc-4b3a-b5e1-c6b1c0c3aa78

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (W : Submodule ℂ (Fin t → ℂ)) :
    ringKrullDim
      (MvPolynomial (Fin t) ℂ ⧸
        MvPolynomial.vanishingIdeal ℂ (W : Set (Fin t → ℂ))) =
      (↑(Module.finrank ℂ W) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv
    (submoduleVanishingIdealCoordinateRingEquiv W).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simp
end PermanentRollout
