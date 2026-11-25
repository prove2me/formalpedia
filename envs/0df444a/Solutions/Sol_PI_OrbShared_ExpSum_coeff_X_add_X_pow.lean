-- Prove2me | solution 1 for PI.OrbShared.ExpSum.coeff_X_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:18.006698+00:00
-- url     : https://prove2.me/submissions/38045db0-54d6-48a1-939f-84127357baf5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_fin_two_vector_eq_matrixVecCons

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
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
namespace PI.OrbShared.ExpSum
theorem _root_.solution (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : K) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1), coeff e ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (n - m) *
      (n.choose m : MvPowerSeries (Fin 2) K)) = if e 0 = m ∧ e 1 = n - m then (n.choose m : K) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, X_pow_eq, X_pow_eq, monomial_mul_monomial, coeff_monomial,
      mul_one, nsmul_eq_mul]
    simp only [fin_two_vector_eq_matrixVecCons]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · rw [Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hb h1.symm
    · intro hb
      exfalso
      apply hb
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [Finset.mem_range] at hm
    omega
end PI.OrbShared.ExpSum
