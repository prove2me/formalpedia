-- Prove2me | solution 1 for PI.UnitKronW.form_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:58.809481+00:00
-- url     : https://prove2.me/submissions/dbce8e99-86bd-4951-87e6-32ea3fe8769d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (x y : Fin k → ℂ) :
    star (G *ᵥ x) ⬝ᵥ (H *ᵥ (G *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
  conv_rhs => rw [← hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
end PI.UnitKronW
