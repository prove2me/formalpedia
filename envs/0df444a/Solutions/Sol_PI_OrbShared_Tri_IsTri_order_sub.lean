-- Prove2me | solution 1 for PI.OrbShared.Tri.IsTri.order_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:29.594484+00:00
-- url     : https://prove2.me/submissions/bd30fa75-fd8c-4b3b-b2f5-edf828812e83

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
theorem _root_.solution (ha : IsTri c a) (v : σ) : ((2 : ℕ) : ℕ∞) ≤ (a v - C c * X v).order := by
  refine le_order fun n hn => ?_
  have hn' : n.degree ≤ 1 := by
    have : (n.degree : ℕ∞) < ((2 : ℕ) : ℕ∞) := hn
    norm_cast at this
    omega
  rw [map_sub, ha v n hn', coeff_C_mul, coeff_X]
  split_ifs <;> simp
end IsTri
end PI.OrbShared.Tri
