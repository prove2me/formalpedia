-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:44.645121+00:00
-- url     : https://prove2.me/submissions/946eed3b-bfcc-4faa-a6f2-7e7e298f04b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_C

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
theorem _root_.solution : Good (R := R) wt δ 0 1 := by
  simpa using good_C (δ := δ) (isWeightedHomogeneous_one (R := R) (w := wt))
end PI.OddDualWeyl.Hom
