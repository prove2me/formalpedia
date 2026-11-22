-- Prove2me | solution 1 for PI.OrbShared.Tri.IsTri.constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:19.270132+00:00
-- url     : https://prove2.me/submissions/6a81a7c7-ed37-4a22-b011-6e0eaed622a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}
namespace PI.OrbShared.Tri
namespace IsTri
theorem _root_.solution (ha : IsTri c a) (v : σ) : constantCoeff (a v) = 0 := by
  have h := ha v 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h, if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]
end IsTri
end PI.OrbShared.Tri
