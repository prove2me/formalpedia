-- Prove2me | solution 1 for ProjSchedTW.NetPresentValue.npv_binary_monotone_sum_separable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:34:30.294276+00:00
-- url     : https://prove2.me/submissions/908664b3-4f01-4ca2-91db-c88115af88e0

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_NetPresentValue_Objective

set_option autoImplicit false

open ProjSchedTW.NetPresentValue in
lemma npv33914856_line {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β)
    (c : Fin (n + 2) → ℝ) (S z : Fin (n + 2) → ℝ) (hz : ∀ i, z i = 0 ∨ z i = 1) (t : ℝ) :
    npvObjective P β c (S + t • z) =
      -(∑ i, c i * β ^ (S i + (P.p i : ℝ)) * (1 - z i))
        - (∑ i, c i * β ^ (S i + (P.p i : ℝ)) * z i) * β ^ t := by
  have key : ∀ i, c i * β ^ ((S + t • z) i + (P.p i : ℝ)) =
      c i * β ^ (S i + (P.p i : ℝ)) * (1 - z i) + c i * β ^ (S i + (P.p i : ℝ)) * z i * β ^ t := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hz i with h | h <;> rw [h]
    · simp
    · rw [show S i + t * 1 + (P.p i : ℝ) = (S i + (P.p i : ℝ)) + t by ring, Real.rpow_add hβ0]
      ring
  unfold npvObjective
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_mul]
  ring

open ProjSchedTW.NetPresentValue in
theorem solution {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (c : Fin (n + 2) → ℝ) :
    IsBinaryMonotone (npvObjective P β c) ∧ IsSumSeparable (npvObjective P β c) := by
  constructor
  · intro S z hz
    have hf : (fun t : ℝ => npvObjective P β c (S + t • z)) = fun t : ℝ =>
        -(∑ i, c i * β ^ (S i + (P.p i : ℝ)) * (1 - z i))
          - (∑ i, c i * β ^ (S i + (P.p i : ℝ)) * z i) * β ^ t :=
      funext (npv33914856_line P β hβ0 c S z hz)
    rw [hf]
    rcases le_total (∑ i, c i * β ^ (S i + (P.p i : ℝ)) * z i) 0 with hB | hB
    · right
      intro x _ y _ hxy
      have h := Real.rpow_le_rpow_of_exponent_ge hβ0 hβ1 hxy
      have := mul_le_mul_of_nonpos_left h hB
      simp only
      linarith
    · left
      intro x _ y _ hxy
      have h := Real.rpow_le_rpow_of_exponent_ge hβ0 hβ1 hxy
      have := mul_le_mul_of_nonneg_left h hB
      simp only
      linarith
  · refine ⟨fun i s => -(c i * β ^ (s + (P.p i : ℝ))), fun S _ => ?_⟩
    unfold npvObjective
    rw [Finset.sum_neg_distrib]
