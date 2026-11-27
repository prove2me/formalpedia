-- Prove2me | solution 1 for PI.OrbShared.Tri.surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:31.040235+00:00
-- url     : https://prove2.me/submissions/4542fe7c-19fe-44d2-a716-e10ad4a56c43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_subst_sol

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
theorem _root_.solution (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) :
    ∃ F : MvPowerSeries σ K, subst a F = G :=
  ⟨sol c a G, subst_sol hc ha G⟩
end PI.OrbShared.Tri
