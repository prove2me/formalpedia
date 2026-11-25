-- Prove2me | solution 1 for PI.FglShared.int_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:59.639797+00:00
-- url     : https://prove2.me/submissions/f5f51bbb-3da2-41c9-bf60-ec63dcca4fcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {σ : Type} [DecidableEq σ] {u n : MvPowerSeries σ ℂ_[p]}
    (hn : ∀ α, ‖coeff α n‖ ≤ 1) (hn0 : constantCoeff n = 1) (h : u * n = 1) :
    ∀ α, ‖coeff α u‖ ≤ 1 := by
  have hn0' : coeff 0 n = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hn0]
  suffices H : ∀ d : ℕ, ∀ α : σ →₀ ℕ, Finsupp.degree α = d → ‖coeff α u‖ ≤ 1 from
    fun α => H _ α rfl
  intro d
  induction d using Nat.strong_induction_on
  rename_i d ih
  intro α hd
  have hmem : (α, (0 : σ →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal α := by simp
  have key : coeff α u + ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n =
      coeff α (1 : MvPowerSeries σ ℂ_[p]) := by
    rw [← h, coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    simp [hn0', hn0]
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal α).erase (α, 0), coeff x.1 u * coeff x.2 n‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro x hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h2 : x.2 ≠ 0 := by
      intro h0
      exact hne (Prod.ext (by simpa [h0] using hx) (by simpa using h0))
    have hdeg : Finsupp.degree x.1 < d := by
      have hsum := congrArg Finsupp.degree hx
      rw [map_add] at hsum
      have : Finsupp.degree x.2 ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
      omega
    rw [norm_mul]
    exact mul_le_one₀ (ih _ hdeg x.1 rfl) (norm_nonneg _) (hn _)
  rw [eq_sub_of_add_eq key, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_one]
    split_ifs <;> simp
  · rwa [norm_neg]
end PI.FglShared
