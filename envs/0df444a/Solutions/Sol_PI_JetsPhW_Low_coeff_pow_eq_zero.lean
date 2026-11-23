-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:02.430889+00:00
-- url     : https://prove2.me/submissions/400fcd3c-657d-4deb-a000-a6da47c839aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]
namespace PI.JetsPhW.Low
theorem _root_.solution {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    ∀ (d : ℕ) (e : σ →₀ ℕ), Finsupp.degree e < d → MvPowerSeries.coeff e (A ^ d) = 0
  | 0, e, h => absurd h (Nat.not_lt_zero _)
  | d + 1, e, h => by
    classical
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hx1 : x.1 = 0
    · rw [hx1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    · have h1 : 1 ≤ Finsupp.degree x.1 := by
        rw [Nat.one_le_iff_ne_zero]
        intro h0
        exact hx1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have h2 : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree e := by
        rw [← map_add, hx]
      rw [solution hA d x.2 (by omega), mul_zero]
end PI.JetsPhW.Low
