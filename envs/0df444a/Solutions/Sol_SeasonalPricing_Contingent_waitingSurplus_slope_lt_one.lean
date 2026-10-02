-- Prove2me | solution 1 for SeasonalPricing.Contingent.waitingSurplus_slope_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:56:43.211161+00:00
-- url     : https://prove2.me/submissions/6628db09-07f2-4277-b395-b84c702cb62c

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

set_option autoImplicit false

namespace SeasonalPricing.Contingent

lemma wsl_term_lower (w δ ψ ψ' p : ℝ) (hw : 0 ≤ w) (hδ : 0 < δ) (h : ψ ≤ ψ') :
    (if p ≤ ψ * δ then δ * (ψ' - ψ) * w else 0)
      ≤ w * max (ψ' * δ - p) 0 - w * max (ψ * δ - p) 0 := by
  have hm : ψ * δ ≤ ψ' * δ := mul_le_mul_of_nonneg_right h hδ.le
  split_ifs with hp
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    nlinarith
  · have := mul_le_mul_of_nonneg_left
      (max_le_max (show ψ * δ - p ≤ ψ' * δ - p by linarith) (le_refl (0:ℝ))) hw
    linarith

lemma wsl_term_upper (w δ ψ ψ' p : ℝ) (hw : 0 ≤ w) (hδ : 0 < δ) (h : ψ ≤ ψ') :
    w * max (ψ' * δ - p) 0 - w * max (ψ * δ - p) 0
      ≤ (if p ≤ ψ' * δ then δ * (ψ' - ψ) * w else 0) := by
  have hm : ψ * δ ≤ ψ' * δ := mul_le_mul_of_nonneg_right h hδ.le
  split_ifs with hp
  · rw [max_eq_left (by linarith)]
    have := mul_le_mul_of_nonneg_left (le_max_left (ψ * δ - p) 0) hw
    nlinarith
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp

end SeasonalPricing.Contingent

open SeasonalPricing.Contingent in
theorem solution (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    (∀ ψ ψ' : ℝ, ψ ≤ ψ' →
      0 ≤ waitingSurplus Q pmf alloc p2 α T t ψ ∧
      waitingSurplus Q pmf alloc p2 α T t ψ ≤ waitingSurplus Q pmf alloc p2 α T t ψ' ∧
      Real.exp (-(α * (T - t))) * (ψ' - ψ) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ * Real.exp (-(α * (T - t)))), pmf q * alloc q)
        ≤ waitingSurplus Q pmf alloc p2 α T t ψ' - waitingSurplus Q pmf alloc p2 α T t ψ ∧
      waitingSurplus Q pmf alloc p2 α T t ψ' - waitingSurplus Q pmf alloc p2 α T t ψ
        ≤ Real.exp (-(α * (T - t))) * (ψ' - ψ) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ' * Real.exp (-(α * (T - t)))), pmf q * alloc q)) ∧
    (∀ ψ : ℝ,
      Real.exp (-(α * (T - t))) *
          (∑ q ∈ (Finset.range (Q + 1)).filter
              (fun q => p2 q ≤ ψ * Real.exp (-(α * (T - t)))), pmf q * alloc q) < 1) := by
  obtain ⟨hpmf0, hpmf1, halloc, -⟩ := hbelief
  set δ := Real.exp (-(α * (T - t))) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hw : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q := fun q hq =>
    mul_nonneg (hpmf0 q hq) (halloc q hq).1
  have hfilt : ∀ c d : ℝ, d * (∑ q ∈ (Finset.range (Q + 1)).filter (fun q => p2 q ≤ c),
      pmf q * alloc q) = ∑ q ∈ Finset.range (Q + 1),
        (if p2 q ≤ c then d * (pmf q * alloc q) else 0) := by
    intro c d
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · intro ψ ψ' h
    have hm : ψ * δ ≤ ψ' * δ := mul_le_mul_of_nonneg_right h hδ.le
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold waitingSurplus
      exact Finset.sum_nonneg fun q hq => mul_nonneg (hw q hq) (le_max_right _ _)
    · unfold waitingSurplus
      refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (hw q hq)
      exact max_le_max (by linarith) le_rfl
    · rw [hfilt]
      unfold waitingSurplus
      rw [← hδdef, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun q hq => ?_
      have := wsl_term_lower (pmf q * alloc q) δ ψ ψ' (p2 q) (hw q hq) hδ h
      simpa [mul_assoc] using this
    · rw [hfilt]
      unfold waitingSurplus
      rw [← hδdef, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun q hq => ?_
      have := wsl_term_upper (pmf q * alloc q) δ ψ ψ' (p2 q) (hw q hq) hδ h
      simpa [mul_assoc] using this
  · intro ψ
    have hS0 : 0 ≤ ∑ q ∈ (Finset.range (Q + 1)).filter (fun q => p2 q ≤ ψ * δ),
        pmf q * alloc q :=
      Finset.sum_nonneg fun q hq => hw q (Finset.mem_of_mem_filter q hq)
    have hSW : ∑ q ∈ (Finset.range (Q + 1)).filter (fun q => p2 q ≤ ψ * δ),
        pmf q * alloc q ≤ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun q hq _ => hw q hq)
    have hW1 : ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q ≤ 1 := by
      rw [← hpmf1]
      refine Finset.sum_le_sum fun q hq => ?_
      have := mul_le_mul_of_nonneg_left (halloc q hq).2 (hpmf0 q hq)
      linarith
    have hTt : 0 < T - t := by linarith
    rcases hslope with hα' | hs
    · have hδ1 : δ < 1 := by
        rw [hδdef]
        rw [Real.exp_lt_one_iff]
        have := mul_pos hα' hTt
        linarith
      nlinarith
    · have hδ1 : δ ≤ 1 := by
        rw [hδdef, Real.exp_le_one_iff]
        have := mul_nonneg hα hTt.le
        linarith
      nlinarith
