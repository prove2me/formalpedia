-- Prove2me | solution 1 for PI.LatIdxDetW.lidx_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:41.837366+00:00
-- url     : https://prove2.me/submissions/b02ae21f-5ff7-4ad7-bac8-615ebf95179e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_PI_LatIdxDetW_locLen_map

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (A B : Submodule R W) :
    lidx p (A.map (φ : W →ₗ[R] W')) (B.map (φ : W →ₗ[R] W')) = lidx p A B := by
  unfold lidx
  rw [← Submodule.map_inf _ φ.injective, locLen_map, locLen_map]
end PI.LatIdxDetW
