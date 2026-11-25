-- Prove2me | solution 1 for PI.FglPhSplit.Wk.expMv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:41.11784+00:00
-- url     : https://prove2.me/submissions/9332e94d-b057-49c5-adb1-f3b0adc7c48f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Theorems.Thm_PI_FglPhSplit_Wk_coeff_pow_mul_pow_eq_zero
import Theorems.Thm_PI_FglPhSplit_Wk_coeff_expT
import Theorems.Thm_PI_FglPhSplit_Wk_coeff_expMv_eq_expT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
private theorem coeff_expT_add_eq_coeff_expT_mul_expT [CharZero K] {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (f + g) N) = coeff α (expT f N * expT g N) := by
  set F : ℕ → ℕ → K := fun i j =>
    coeff α (f ^ i * g ^ j) / ((i.factorial : K) * (j.factorial : K)) with hF
  have hfac : ∀ n : ℕ, (n.factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have lhs : coeff α (expT (f + g) N) = ∑ n ∈ range N, ∑ m ∈ range (n + 1), F m (n - m) := by
    rw [coeff_expT]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_pow, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hc : ((n.choose m : ℕ) : K) * (m.factorial : K) * ((n - m).factorial : K) =
        (n.factorial : K) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)), coeff_mul_C]
    show _ = coeff α (f ^ m * g ^ (n - m)) / ((m.factorial : K) * ((n - m).factorial : K))
    rw [← hc]
    have := hfac m
    have := hfac (n - m)
    have hch : ((n.choose m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hmn).ne'
    field_simp
  have rhs : coeff α (expT f N * expT g N) = ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
    simp only [expT]
    rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, map_smul, smul_eq_mul]
    show _ = coeff α (f ^ i * g ^ j) / ((i.factorial : K) * (j.factorial : K))
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [lhs, rhs, Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    show coeff α (f ^ i * g ^ j) / _ = 0
    rw [coeff_pow_mul_pow_eq_zero hf hg (by omega), zero_div]
end PI.FglPhSplit.Wk
end
end

set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
namespace PI.FglPhSplit.Wk
theorem _root_.solution [CharZero K] {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
  classical
  ext α
  have hfg : constantCoeff (f + g) = 0 := by rw [map_add, hf, hg, add_zero]
  rw [coeff_expMv_eq_expT hfg (Nat.lt_succ_self (Finsupp.degree α)), coeff_mul]
  have key : ∀ p ∈ antidiagonal α, coeff p.1 (expMv f) * coeff p.2 (expMv g) =
      coeff p.1 (expT f (Finsupp.degree α + 1)) * coeff p.2 (expT g (Finsupp.degree α + 1)) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
      rw [← hp, map_add]
    rw [coeff_expMv_eq_expT hf (N := Finsupp.degree α + 1) (by omega),
      coeff_expMv_eq_expT hg (N := Finsupp.degree α + 1) (by omega)]
  rw [Finset.sum_congr rfl key, ← coeff_mul]
  exact coeff_expT_add_eq_coeff_expT_mul_expT hf hg (Nat.lt_succ_self _)
end PI.FglPhSplit.Wk
