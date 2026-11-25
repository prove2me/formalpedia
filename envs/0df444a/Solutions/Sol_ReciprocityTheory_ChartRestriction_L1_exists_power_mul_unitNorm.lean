-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_power_mul_unitNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:28.069464+00:00
-- url     : https://prove2.me/submissions/884bff97-fb57-4e70-a2f0-3a6a28074b40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_norm_le
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_l_Cl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_frob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  induction k with
  | zero =>
    intro a ha _ h
    rw [pow_zero, one_mul] at h
    exact absurd (rmu_norm_le l ha) (not_le.2 h)
  | succ k ih =>
    intro a ha ha0 h
    rcases (rmu_norm_le l ha).eq_or_lt with h1 | h1
    · exact ⟨0, a, ha, 1, (Rmu l).one_mem, h1, norm_one, by rw [pow_zero, one_mul, mul_one]⟩
    obtain ⟨f, hf, r, hr, he⟩ := rmu_frob l a ha
    have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
    have hq : 1 ≤ l ^ f - 1 := by
      have : 2 ≤ l ^ f := le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow hf.ne' l)
      omega
    set u := a ^ (l ^ f - 1) - 1 with hu
    have huR : u ∈ Rmu l := sub_mem (pow_mem ha _) (Rmu l).one_mem
    have hu1 : ‖u‖ = 1 := by
      have hsm : ‖a ^ (l ^ f - 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) h1 (by omega)
      have := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_eq_of_norm_sub_lt' l (a := u) (b := -1)
        (by rw [hu, sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one]; exact hsm)
      rwa [norm_neg, norm_one] at this
    have hau : a * u = (l : ℂ_[l]) * r := by
      rw [← he, hu, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l ^ f)]
    have hnr : ‖r‖ = l * ‖a‖ := by
      have := congrArg norm hau
      rw [norm_mul, norm_mul, hu1, mul_one, norm_l_Cl] at this
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      rw [this, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hnr
      have : (0 : ℝ) < l * ‖a‖ := mul_pos (by positivity) (norm_pos_iff.2 ha0)
      linarith
    have h' : 1 < (l : ℝ) ^ k * ‖r‖ := by
      rw [hnr, ← mul_assoc, ← pow_succ]; exact h
    obtain ⟨m, c, hc, v, hv, hc1, hv1, hrv⟩ := ih r hr hr0 h'
    refine ⟨m + 1, c, hc, u * v, mul_mem huR hv, hc1, by rw [norm_mul, hu1, hv1, one_mul], ?_⟩
    rw [← mul_assoc, hau, mul_assoc, hrv, pow_succ]
    ring
end ReciprocityTheory.ChartRestriction.L1
