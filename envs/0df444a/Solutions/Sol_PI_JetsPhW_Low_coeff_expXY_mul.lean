-- Prove2me | solution 1 for PI.JetsPhW.Low.coeff_expXY_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:40.832114+00:00
-- url     : https://prove2.me/submissions/8ea2dd04-b191-4157-a605-d98c62f5421b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Theorems.Thm_PI_JetsPhW_Low_expX_ne_expY
import Theorems.Thm_PI_JetsPhW_Low_eq_of_add_eq_expXY

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
theorem _root_.solution {A B : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.coeff bivariateExponentMonomial (A * B) =
      MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B +
        MvPowerSeries.coeff E1 A * MvPowerSeries.coeff E0 B := by
  classical
  rw [MvPowerSeries.coeff_mul]
  have hsub : ({(E0, E1), (E1, E0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) ⊆
      Finset.HasAntidiagonal.antidiagonal bivariateExponentMonomial := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rcases hq with rfl | rfl
    · rfl
    · exact add_comm _ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_pair (fun h => expX_ne_expY (congrArg Prod.fst h))]
  · intro q hq hq'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    by_cases h1 : q.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    by_cases h2 : q.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]
    exfalso
    apply hq'
    rcases eq_of_add_eq_expXY hq h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
    · simp [Prod.ext_iff, a, b]
    · simp [Prod.ext_iff, a, b]
end PI.JetsPhW.Low
