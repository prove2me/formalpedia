-- Prove2me | solution 1 for PI.LatIdxDetW.locLen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:57.899968+00:00
-- url     : https://prove2.me/submissions/2677e7d1-a1c8-4c35-97ac-2fe066112b88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_P2M_PI_LatIdxDetW_localization_map__381d41331f98
import Theorems.Thm_PI_LatIdxDetW_length_map

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (X Y : Submodule R W) :
    locLen p (X.map (φ : W →ₗ[R] W')) (Y.map (φ : W →ₗ[R] W')) = locLen p X Y := by
  unfold locLen
  rw [localization_map₂, localization_map₂, length_map]
end PI.LatIdxDetW
