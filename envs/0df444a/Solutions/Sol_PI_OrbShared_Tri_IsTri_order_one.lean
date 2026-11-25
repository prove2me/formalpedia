-- Prove2me | solution 1 for PI.OrbShared.Tri.IsTri.order_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:26.18958+00:00
-- url     : https://prove2.me/submissions/6ec50d40-df31-4782-aa57-7e4902ef9bf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_IsTri_constantCoeff

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
theorem _root_.solution (ha : IsTri c a) (v : σ) : 1 ≤ (a v).order :=
  one_le_order_iff_constCoeff_eq_zero.mpr (ha.constantCoeff v)
end IsTri
end PI.OrbShared.Tri
