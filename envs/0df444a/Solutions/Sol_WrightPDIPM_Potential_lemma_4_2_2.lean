-- Prove2me | solution 2 for WrightPDIPM.Potential.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:54.446666+00:00
-- url     : https://prove2.me/submissions/f8181abd-aa03-4277-9785-216acf3bc6fa

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
set_option autoImplicit false
open WrightPDIPM.Potential

theorem solution {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) :
    (n : ℝ) * Real.log n ≤ Phi (n : ℝ) x s ∧
      (Phi (n : ℝ) x s = (n : ℝ) * Real.log n ↔ ∀ i, x i * s i = mu x s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Phi, mu]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpp : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have hdot : x ⬝ᵥ s = ∑ i, x i * s i := rfl
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hSpos : 0 < ∑ i, x i * s i := Finset.sum_pos (fun i _ => hpp i) Finset.univ_nonempty
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = mu x s := ⟨_, rfl⟩
  have hμdef : μ = (∑ i, x i * s i) / n := by rw [hμ]; rfl
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  have hsum : ∑ i, x i * s i = n * μ := by rw [hμdef]; field_simp
  have hlog : ∀ i, Real.log (x i * s i) ≤ Real.log μ + (x i * s i / μ - 1) := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (hpp i) hμpos)
    rw [Real.log_div (hpp i).ne' hμpos.ne'] at this
    linarith
  have hPhi : Phi (n : ℝ) x s = n * Real.log n + n * Real.log μ - ∑ i, Real.log (x i * s i) := by
    unfold Phi
    rw [hdot, hsum, Real.log_mul hn'.ne' hμpos.ne']
    ring
  have hsumeq : ∑ i, (Real.log μ + (x i * s i / μ - 1)) = n * Real.log μ := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Finset.sum_div, hsum]
    field_simp
    ring
  have hsumlog : ∑ i, Real.log (x i * s i) ≤ n * Real.log μ := by
    rw [← hsumeq]
    exact Finset.sum_le_sum (fun i _ => hlog i)
  refine ⟨by rw [hPhi]; linarith, ?_⟩
  rw [← hμ]
  constructor
  · intro h i
    by_contra hne
    have hlt : Real.log (x i * s i) < Real.log μ + (x i * s i / μ - 1) := by
      have hne' : x i * s i / μ ≠ 1 := by
        intro h1
        apply hne
        field_simp at h1
        exact h1
      have := Real.log_lt_sub_one_of_pos (div_pos (hpp i) hμpos) hne'
      rw [Real.log_div (hpp i).ne' hμpos.ne'] at this
      linarith
    have hstrict : ∑ i, Real.log (x i * s i) < ∑ i, (Real.log μ + (x i * s i / μ - 1)) :=
      Finset.sum_lt_sum (fun j _ => hlog j) ⟨i, Finset.mem_univ i, hlt⟩
    rw [hsumeq] at hstrict
    rw [hPhi] at h
    linarith
  · intro h
    rw [hPhi]
    have : ∑ i, Real.log (x i * s i) = n * Real.log μ := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [h i])]
      simp
    rw [this]
    ring
