-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.tch_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:26.986413+00:00
-- url     : https://prove2.me/submissions/26efbb5a-0e87-4945-9e61-662f52555768

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_sub_le_max_Cl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_Cl_of_not_dvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muP_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_exists_root_near
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_geom_sum_eq_one


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
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hq : 2 ≤ l ^ f := le_trans hl (Nat.le_self_pow hf.ne' l)
  obtain ⟨m, hm⟩ : ∃ m, l ^ f = m + 1 := ⟨l ^ f - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hlm : ¬ l ∣ m := by
    intro hd
    have h1 : l ∣ m + 1 := hm ▸ dvd_pow_self l hf.ne'
    have h2 : l ∣ 1 := (Nat.dvd_add_right hd).1 h1
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  by_cases hsmall : ‖x‖ ≤ r
  · exact ⟨0, Set.mem_insert _ _, by simpa using hsmall⟩
  push Not at hsmall
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) h
  have hx1 : ‖x‖ = 1 := by
    have h1 : ‖x‖ ≤ max ‖x ^ (l ^ f)‖ ‖x ^ (l ^ f) - x‖ := by
      calc ‖x‖ = ‖x ^ (l ^ f) - (x ^ (l ^ f) - x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le_max_Cl l _ _
    have h2 : ‖x‖ ≤ ‖x‖ ^ (l ^ f) := by
      rw [← norm_pow]
      rcases le_max_iff.1 h1 with h3 | h3
      · exact h3
      · linarith
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hr0 hsmall
    have := pow_lt_self_of_lt_one₀ hpos hlt (by omega : 1 < l ^ f)
    linarith
  have hxm : ‖x ^ m - 1‖ ≤ r := by
    have e : x ^ (l ^ f) - x = x * (x ^ m - 1) := by rw [hm]; ring
    rwa [e, norm_mul, hx1, one_mul] at h
  obtain ⟨ζ, hζroot, hζ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ m - C 1)
    (monic_X_pow_sub_C 1 hm0.ne') x
    (by simp only [eval_sub, eval_pow, eval_X, eval_C]; exact lt_of_le_of_lt hxm hr)
  have hζm : ζ ^ m = 1 := by
    have : ζ ^ m - 1 = 0 := by simpa using hζroot
    exact sub_eq_zero.1 this
  have hmu : ζ ∈ muP l := ⟨m, hm0, hlm, hζm⟩
  refine ⟨ζ, Set.mem_insert_of_mem _ hmu, ?_⟩
  have hζ1 : ‖ζ‖ = 1 := muP_norm l hmu
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have e1 : x - ζ = ζ * (x * ζ⁻¹ - 1) := by
    rw [mul_sub, mul_one, mul_comm x ζ⁻¹, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have e2 : x ^ m - 1 = (∑ i ∈ Finset.range m, (x * ζ⁻¹) ^ i) * (x * ζ⁻¹ - 1) := by
    rw [geom_sum_mul, mul_pow, inv_pow, hζm, inv_one, mul_one]
  have hy : ‖x * ζ⁻¹ - 1‖ = ‖x - ζ‖ := by rw [e1, norm_mul, hζ1, one_mul]
  rw [e2, norm_mul, ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one l (hy ▸ hζ)
    (norm_natCast_Cl_of_not_dvd l hlm), one_mul, hy] at hxm
  exact hxm
end ReciprocityTheory.ChartRestriction.L1
