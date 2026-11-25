-- Prove2me | solution 1 for PI.FglPhSplit.Wk.coeff_pow_mul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:23.298365+00:00
-- url     : https://prove2.me/submissions/ff0ef0df-b173-47d0-93c2-6a780d650141

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
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
private theorem coeff_pow_eq_zero_of_degree_lt_formal_group_splitting {f : MvPowerSeries σ K} (hf : constantCoeff f = 0) :
    ∀ (n : ℕ) {α : σ →₀ ℕ}, Finsupp.degree α < n → coeff α (f ^ n) = 0 := by
  classical
  intro n
  induction n with
  | zero => intro α h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro α h
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h2 : p.2 = 0
    · rw [h2, coeff_zero_eq_constantCoeff_apply, hf, mul_zero]
    · have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
        rw [← hp, map_add]
      have h2' : 0 < Finsupp.degree p.2 := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact h2 ((Finsupp.degree_eq_zero_iff _).mp h0)
      rw [ih (by omega), zero_mul]
end PI.FglPhSplit.Wk
end
end

set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
namespace PI.FglPhSplit.Wk
theorem _root_.solution {f g : MvPowerSeries σ K} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) {i j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < i + j) :
    coeff α (f ^ i * g ^ j) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← hp, map_add]
  by_cases h1 : Finsupp.degree p.1 < i
  · rw [coeff_pow_eq_zero_of_degree_lt_formal_group_splitting hf i h1, zero_mul]
  · rw [coeff_pow_eq_zero_of_degree_lt_formal_group_splitting hg j (by omega), mul_zero]
end PI.FglPhSplit.Wk
