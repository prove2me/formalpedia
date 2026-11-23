-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.deg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:43.403412+00:00
-- url     : https://prove2.me/submissions/c1da34ac-569a-476f-8ca8-6bb604bb4309

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
variable {σ : Type*} {A : Type*} [CommRing A]
namespace PI.UnitaryGroupMassFormula.TayInvPow
theorem _root_.solution {β : σ →₀ ℕ} : deg β = 0 ↔ β = 0 := by
  unfold deg
  rw [Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext i
    by_cases hi : i ∈ β.support
    · exact h i hi
    · simpa using hi
  · rintro rfl
    simp
end PI.UnitaryGroupMassFormula.TayInvPow
