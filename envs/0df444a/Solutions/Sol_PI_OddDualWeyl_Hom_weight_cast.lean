-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.weight_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:02.674346+00:00
-- url     : https://prove2.me/submissions/743b440e-618a-4d76-8528-877b14ed386f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity

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
theorem _root_.solution (w : Fin k × Fin k → ℕ) (α : Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (fun v => (w v : ℤ)) α = (Finsupp.weight w α : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
end PI.OddDualWeyl.Hom
