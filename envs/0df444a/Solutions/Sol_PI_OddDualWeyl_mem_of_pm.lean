-- Prove2me | solution 1 for PI.OddDualWeyl.mem_of_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:04.817184+00:00
-- url     : https://prove2.me/submissions/a5f127b0-3565-4c2b-895c-48dd82bce587

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
variable {R : Type} [CommRing R] {k M : ℕ}
namespace PI.OddDualWeyl
theorem _root_.solution {S : Submodule R (MvPolynomial (Fin k × Fin k) R)} {x : MvPolynomial (Fin k × Fin k) R}
    (u : MvPolynomial (Fin k × Fin k) R) (hu : u = 1 ∨ u = -1) (hx : x ∈ S) : u * x ∈ S := by
  rcases hu with rfl | rfl
  · rw [one_mul]; exact hx
  · rw [neg_one_mul]; exact S.neg_mem hx
end PI.OddDualWeyl
