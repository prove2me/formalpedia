-- Prove2me | solution 1 for PI.JetsPhW.Low.pcoeff2_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:06.8042+00:00
-- url     : https://prove2.me/submissions/3e7aabed-3fc7-4924-99fe-3ee68e7d987c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_coeff_subst_low

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
theorem _root_.solution {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 2 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 2 A +
        PowerSeries.coeff 2 f * (PowerSeries.coeff 1 A) ^ 2 := by
  have h := coeff_subst_low (σ := Unit) hA f (e := Finsupp.single () 2)
    (by simp) (by rw [Finsupp.degree_single])
  have h2 : PowerSeries.coeff 2 (A ^ 2) = (PowerSeries.coeff 1 A) ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [hA]
    ring
  rw [← h2]
  exact h
end PI.JetsPhW.Low
