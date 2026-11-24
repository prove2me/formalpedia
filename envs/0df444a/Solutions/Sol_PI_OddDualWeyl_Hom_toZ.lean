-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.toZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.953961+00:00
-- url     : https://prove2.me/submissions/838fa34a-630d-444d-b8f6-35aa610f4bae

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
theorem _root_.solution {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {d : ℕ}
    (h : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous (fun v => (w v : ℤ)) f (d : ℤ) := by
  intro α hα
  rw [weight_cast, h hα]
end PI.OddDualWeyl.Hom
