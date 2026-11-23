-- Prove2me | solution 1 for PI.OrbShared.Tri.ord_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:27.634961+00:00
-- url     : https://prove2.me/submissions/451fd320-bfb5-49b0-9067-a9ae6d305ba8

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
theorem _root_.solution {f g : MvPowerSeries σ K} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    (n : ℕ∞) ≤ (f + g).order :=
  (le_min hf hg).trans min_order_le_add
end PI.OrbShared.Tri
