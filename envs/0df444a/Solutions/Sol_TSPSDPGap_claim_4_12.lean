-- Prove2me | solution 1 for TSPSDPGap.claim_4_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:35:11.227056+00:00
-- url     : https://prove2.me/submissions/d4ae00e9-fa0c-4824-9bea-067134d4c783

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

namespace Aux_C412

open Finset

lemma reflect_sum (g : ℕ) (θ : ℝ) :
    ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ) = ∑ d ∈ Finset.Ico 1 (g + 1), Real.cos ((d:ℝ) * θ) := by
  rw [Finset.sum_Ico_eq_sum_range, show g + 1 - 1 = g by omega]
  rw [← Finset.sum_range_reflect (fun k => Real.cos (((1 + k : ℕ) : ℝ) * θ)) g]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  have e : ((1 + (g - 1 - j) : ℕ) : ℝ) = (g:ℝ) - j := by
    rw [show 1 + (g - 1 - j) = g - j by omega, Nat.cast_sub hj'.le]
  rw [e]

lemma fejer (g : ℕ) (θ : ℝ) :
    (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
      = (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · subst h0
      simp
    have h1 : 1 ≤ g := hpos
    have hsplit : ∑ j ∈ Finset.Ico 1 (g + 1), (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
        = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
          + ∑ j ∈ Finset.Ico 1 (g + 1), Real.cos (j * θ) := by
      rw [Finset.sum_Ico_succ_top h1, Finset.sum_Ico_succ_top h1]
      have e : ∑ j ∈ Finset.Ico 1 g, (((g + 1 : ℕ) : ℝ) - j) * Real.cos (j * θ)
          = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * θ)
            + ∑ j ∈ Finset.Ico 1 g, Real.cos (j * θ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        push_cast
        ring
      rw [e]
      push_cast
      ring
    have hcross : ∑ j ∈ range g, Real.cos (((g:ℝ) - j) * θ)
        = (∑ j ∈ range g, Real.cos (j * θ)) * Real.cos (g * θ)
          + (∑ j ∈ range g, Real.sin (j * θ)) * Real.sin (g * θ) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show ((g:ℝ) - j) * θ = g * θ - j * θ by ring, Real.cos_sub]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsplit, ← reflect_sum, hcross]
    push_cast
    linear_combination ih - Real.sin_sq_add_cos_sq ((g:ℝ) * θ)

lemma fejer_le (g : ℕ) (θ : ℝ) :
    (∑ j ∈ range g, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range g, Real.sin (j * θ)) ^ 2
      ≤ (g:ℝ) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.cos (j * θ))
  have h2 := sq_sum_le_card_mul_sum_sq (s := range g) (f := fun j : ℕ => Real.sin (j * θ))
  have h3 : ∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2 = g := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ range g, Real.cos (j * θ) ^ 2 + Real.sin (j * θ) ^ 2 = 1 := fun j _ => by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq _
    rw [Finset.sum_congr rfl this]
    simp
  simp only [Finset.card_range] at h1 h2
  have h4 : (g:ℝ) * (∑ j ∈ range g, Real.cos (j * θ) ^ 2 + ∑ j ∈ range g, Real.sin (j * θ) ^ 2)
      = (g:ℝ) * g := by rw [h3]
  nlinarith [h1, h2, h4]

/-- Bounds `0 ≤ g + 2P ≤ g²` for the Fejér-type sum appearing in `coeffA`. -/
lemma key (g n i : ℕ) :
    0 ≤ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
    ∧ (g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      ≤ (g : ℝ) ^ 2 := by
  have e : ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
      = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * Real.cos (j * (Real.pi * i / (n / 2 : ℕ))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show Real.pi * (i:ℝ) * (j:ℝ) / ((n / 2 : ℕ) : ℝ)
      = (j:ℝ) * (Real.pi * i / ((n / 2 : ℕ) : ℝ)) by ring]
  rw [e, fejer]
  exact ⟨by positivity, fejer_le g _⟩

lemma circ_nonneg (m i : ℕ) (s t : Fin m) : 0 ≤ circBasis m i s t := by
  unfold circBasis
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

end Aux_C412

end TSPSDPGap

open TSPSDPGap TSPSDPGap.Aux_C412 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffA g n i) ∧
    (∀ i ∈ Finset.Icc 1 (n / 2), 0 ≤ coeffB g n i) ∧
    ∀ a b, 0 ≤ Ymat g n a b := by
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hg1 : (0:ℝ) < (g:ℝ) - 1 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hng : (0:ℝ) < (n:ℝ) - g := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hn0 : (0:ℝ) < n := by
    have : (g:ℝ) < n := by exact_mod_cast hlt
    linarith
  have hgg : (g:ℝ) / g = 1 := div_self hg0.ne'
  have hA : ∀ i, 0 ≤ coeffA g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    unfold coeffA
    split_ifs
    · have e : (2:ℝ) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 2 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = 2 * ((g:ℝ) / g) + 4 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
    · have e : (1:ℝ) + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))
          = 1 / g * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ))) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
            = (g:ℝ) / g + 2 / g * ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
            * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := by ring
        rw [e2, hgg]
      rw [e]
      exact mul_nonneg (one_div_nonneg.2 hng.le) (mul_nonneg (by positivity) k0)
  have hB : ∀ i, 0 ≤ coeffB g n i := by
    intro i
    obtain ⟨k0, k1⟩ := key g n i
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j)
        * Real.cos (Real.pi * i * j / (n / 2 : ℕ)) := ⟨_, rfl⟩
    rw [← hP] at k0 k1
    have hden : 0 < (n:ℝ) * ((g:ℝ) - 1) := mul_pos hn0 hg1
    have hcancel : ∀ X : ℝ, ((n:ℝ) - g) * (1 / ((n:ℝ) - g) * X) = X := by
      intro X
      rw [← mul_assoc, mul_one_div_cancel hng.ne', one_mul]
    unfold coeffB coeffA
    split_ifs with h
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (2:ℝ) + 4 / g * P = 2 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) = 2 * ((g:ℝ) / g) + 4 / g * P := by ring
        rw [e2, hgg, mul_one]
      rw [e]
      have : 2 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 2 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 2 / (g:ℝ) * (g:ℝ) ^ 2 = 2 * g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
    · rw [← hP, hcancel]
      refine div_nonneg ?_ hden.le
      have e : (1:ℝ) + 2 / g * P = 1 / g * ((g : ℝ) + 2 * P) := by
        have e2 : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) = (g:ℝ) / g + 2 / g * P := by ring
        rw [e2, hgg]
      rw [e]
      have : 1 / (g:ℝ) * ((g : ℝ) + 2 * P) ≤ 1 / g * (g:ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
      have e3 : 1 / (g:ℝ) * (g:ℝ) ^ 2 = g * ((g:ℝ) / g) := by ring
      rw [e3, hgg, mul_one] at this
      linarith
  refine ⟨fun i _ => hA i, fun i _ => hB i, ?_⟩
  intro a b
  have hAm : ∀ s t, 0 ≤ Amat g n s t := by
    intro s t
    unfold Amat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hA i) (circ_nonneg n i s t))
  have hBm : ∀ s t, 0 ≤ Bmat g n s t := by
    intro s t
    unfold Bmat
    rw [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_nonneg (hB i) (circ_nonneg n i s t))
  unfold Ymat
  simp only [Matrix.of_apply]
  apply mul_nonneg (by positivity)
  split_ifs
  · norm_num
  · norm_num
  · exact hAm _ _
  · exact hBm _ _
