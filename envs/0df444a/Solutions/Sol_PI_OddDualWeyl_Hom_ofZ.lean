-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.ofZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.769812+00:00
-- url     : https://prove2.me/submissions/f2ffa262-9988-4930-9e30-139ab12dd1e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_weight_cast

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
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {m : ℤ}
    (h : IsWeightedHomogeneous (fun v => (w v : ℤ)) f m) : IsWeightedHomogeneous w f m.toNat := by
  intro α hα
  have := h hα
  rw [weight_cast] at this
  omega
end PI.OddDualWeyl.Hom
