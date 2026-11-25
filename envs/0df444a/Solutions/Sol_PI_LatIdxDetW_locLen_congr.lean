-- Prove2me | solution 1 for PI.LatIdxDetW.locLen_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:09.290521+00:00
-- url     : https://prove2.me/submissions/048577cb-ce7c-4ea5-8e7d-750eca27e094

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace PI.LatIdxDetW
theorem _root_.solution (p : Ideal R) [p.IsPrime] {X X' Y Y' : Submodule R W}
    (hX : localization₂ p X = localization₂ p X') (hY : localization₂ p Y = localization₂ p Y') : locLen p X Y = locLen p X' Y' := by
  unfold locLen
  rw [hX, hY]
end PI.LatIdxDetW
