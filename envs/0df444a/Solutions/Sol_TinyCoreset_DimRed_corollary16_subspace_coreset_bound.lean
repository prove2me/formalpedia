-- Prove2me | solution 1 for TinyCoreset.DimRed.corollary16_subspace_coreset_bound
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:05:20.800497+00:00
-- url     : https://prove2.me/submissions/f982e316-f64c-4adc-bbbd-af0eaf89ea0b

import Theorems.Thm_TinyCoreset_DimRed_sec3_subspace_cost_lower_bound
import Theorems.Thm_TinyCoreset_DimRed_lemma15_residual_sandwich
import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

set_option autoImplicit false

open TinyCoreset
open TinyCoreset.DimRed

open scoped Matrix

open ProjLikeRetr.FixedRank

private theorem svd_threshold {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {U : Matrix (Fin n) (Fin n) ℝ} {S : Matrix (Fin n) (Fin d) ℝ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsSVD A U S V) (j : ℕ) (hj1 : 1 ≤ j) (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    1 ≤ m ∧ (j : ℝ) * sigma S (m + 1) ^ 2 ≤ ε * frobSq (A * Y) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hceilpos := Nat.ceil_pos.mpr (div_pos hjpos hε)
  have hmin : j + 1 ≤ min n d := by omega
  have hm₀ : 1 ≤ m := by omega
  have hjm : j ≤ m + 1 := by omega
  have hcount : (j : ℝ) ≤ ε * ((m + 1 - j : ℕ) : ℝ) := by
    have hceil : (j : ℝ) / ε ≤ (⌈(j : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hnat : ⌈(j : ℝ) / ε⌉₊ ≤ m + 1 - j := by omega
    have hcast : (⌈(j : ℝ) / ε⌉₊ : ℝ) ≤ ((m + 1 - j : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [mul_comm] using (div_le_iff₀ hε).mp (hceil.trans hcast)
  have hmono (i : ℕ) (hi : i ∈ Finset.Icc (j + 1) (m + 1)) :
      sigma S (m + 1) ^ 2 ≤ sigma S i ^ 2 := by
    have ⟨hi₁, hi₂⟩ := Finset.mem_Icc.mp hi
    have hσ₁ : 1 ≤ m + 1 ∧ m + 1 ≤ min n d := ⟨by omega, hmnd⟩
    have hσ₂ : 1 ≤ i ∧ i ≤ min n d := ⟨by omega, hi₂.trans hmnd⟩
    rw [sigma, dif_pos hσ₁, sigma, dif_pos hσ₂]
    apply (sq_le_sq₀ (hA.2.2.2.1 _ _ rfl) (hA.2.2.2.1 _ _ rfl)).2
    exact hA.2.2.2.2.1 _ _ _ _ rfl rfl (by change i - 1 ≤ m + 1 - 1; omega)
  have hcost := TinyCoreset.DimRed.sec3_subspace_cost_lower_bound A U S V hA j hj1 hmin Y hY
  have htail : ((m + 1 - j : ℕ) : ℝ) * sigma S (m + 1) ^ 2 ≤ frobSq (A * Y) := by
    calc
      _ = ∑ _i ∈ Finset.Icc (j + 1) (m + 1), sigma S (m + 1) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hc : m + 1 + 1 - (j + 1) = m + 1 - j := by omega
        rw [hc]
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) (m + 1), sigma S i ^ 2 := Finset.sum_le_sum hmono
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) (min n d), sigma S i ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
        intro i hi
        have h := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hmnd⟩
      _ ≤ _ := hcost
  refine ⟨hm₀, ?_⟩
  calc
    _ ≤ (ε * ((m + 1 - j : ℕ) : ℝ)) * sigma S (m + 1) ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = ε * (((m + 1 - j : ℕ) : ℝ) * sigma S (m + 1) ^ 2) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htail hε.le

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    frobSq (A * Y) ≤ frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V) ∧
    frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V) ≤
        (1 + ε) * frobSq (A * Y) := by
  obtain ⟨hm₀, threshold⟩ := svd_threshold hA j hj1 ε hε m hm hmnd Y hY
  obtain ⟨lower, upper⟩ := lemma15_residual_sandwich A U S V hA j hj1 hjd m hm₀ hmnd Y hY
  constructor
  · linarith
  · have h := upper.trans threshold
    linarith
