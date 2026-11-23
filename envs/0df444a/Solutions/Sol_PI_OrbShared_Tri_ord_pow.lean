-- Prove2me | solution 1 for PI.OrbShared.Tri.ord_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:28.286034+00:00
-- url     : https://prove2.me/submissions/efbdbe84-0618-42cb-a92b-5a9a7e080412

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
theorem _root_.solution {f : MvPowerSeries σ K} (hf : 1 ≤ f.order) (n : ℕ) : (n : ℕ∞) ≤ (f ^ n).order := by
  refine le_trans ?_ (le_order_pow n)
  have := nsmul_le_nsmul_right hf n
  simpa using this
end PI.OrbShared.Tri
