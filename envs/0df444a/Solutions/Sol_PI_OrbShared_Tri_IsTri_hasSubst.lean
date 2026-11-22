-- Prove2me | solution 1 for PI.OrbShared.Tri.IsTri.hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:24.323794+00:00
-- url     : https://prove2.me/submissions/f667c6e5-5ba0-4675-91e7-7d78074ca677

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
theorem _root_.solution (ha : IsTri c a) : HasSubst a :=
  hasSubst_of_constantCoeff_zero fun v => ha.constantCoeff v
end IsTri
end PI.OrbShared.Tri
