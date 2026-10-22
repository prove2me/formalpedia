-- Prove2me | solution 1 for WrightPDIPM.CentralPath.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:38:56.148878+00:00
-- url     : https://prove2.me/submissions/d3416a9e-be4e-4bd0-911e-426ca6a273b5

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP
open WrightPDIPM.CentralPath

open Matrix

theorem g69b_orth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x x' s s' : Fin n → ℝ) (l l' : Fin m → ℝ)
    (hx : A *ᵥ x = b) (hx' : A *ᵥ x' = b) (hs : Aᵀ *ᵥ l + s = c) (hs' : Aᵀ *ᵥ l' + s' = c) :
    x ⬝ᵥ s' + x' ⬝ᵥ s = x ⬝ᵥ s + x' ⬝ᵥ s' := by
  have e1 : x - x' = x - x' := rfl
  have hA : A *ᵥ (x - x') = 0 := by rw [mulVec_sub, hx, hx', sub_self]
  have hS : s - s' = -(Aᵀ *ᵥ (l - l')) := by
    rw [mulVec_sub]
    funext i
    have h1 := congrFun hs i
    have h2 := congrFun hs' i
    simp only [Pi.add_apply] at h1 h2
    simp only [Pi.sub_apply, Pi.neg_apply]
    linarith
  have h0 : (x - x') ⬝ᵥ (s - s') = 0 := by
    rw [hS, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, hA]
    simp
  simp only [sub_dotProduct, dotProduct_sub] at h0
  linarith

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hFo : (Fo A b c).Nonempty) (K : ℝ) (hK : 0 ≤ K) :
    Bornology.IsBounded
      {q : (Fin n → ℝ) × (Fin n → ℝ) | ∃ lam, (q.1, lam, q.2) ∈ F A b c ∧ q.1 ⬝ᵥ q.2 ≤ K} := by
  obtain ⟨⟨xb, lb, sb⟩, ⟨hxb1, hxb2⟩, ⟨hsb1, hsb2⟩⟩ := hFo
  simp only at hxb1 hxb2 hsb1 hsb2
  set M := K + xb ⬝ᵥ sb
  have hM : 0 ≤ M := by
    have : 0 ≤ xb ⬝ᵥ sb := Finset.sum_nonneg (fun j _ => (mul_pos (hxb2 j) (hsb2 j)).le)
    linarith
  set C := ∑ j, M / sb j + ∑ j, M / xb j
  have hC1 : ∀ i, M / sb i ≤ C := by
    intro i
    have := Finset.single_le_sum (f := fun j => M / sb j)
      (fun j _ => div_nonneg hM (hsb2 j).le) (Finset.mem_univ i)
    have : 0 ≤ ∑ j, M / xb j := Finset.sum_nonneg (fun j _ => div_nonneg hM (hxb2 j).le)
    try simp only at *
    linarith
  have hC2 : ∀ i, M / xb i ≤ C := by
    intro i
    have := Finset.single_le_sum (f := fun j => M / xb j)
      (fun j _ => div_nonneg hM (hxb2 j).le) (Finset.mem_univ i)
    have : 0 ≤ ∑ j, M / sb j := Finset.sum_nonneg (fun j _ => div_nonneg hM (hsb2 j).le)
    try simp only at *
    linarith
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro ⟨x, s⟩ ⟨lam, ⟨⟨hx1, hx2⟩, ⟨hs1, hs2⟩⟩, hK'⟩
  simp only at hx1 hx2 hs1 hs2 hK'
  have horth := g69b_orth A b c x xb s sb lam lb hx1 hxb1 hs1 hsb1
  have hsum : x ⬝ᵥ sb + xb ⬝ᵥ s ≤ M := by linarith
  have hn1 : 0 ≤ x ⬝ᵥ sb := Finset.sum_nonneg (fun j _ => mul_nonneg (hx2 j) (hsb2 j).le)
  have hn2 : 0 ≤ xb ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hxb2 j).le (hs2 j))
  have hxi : ∀ i, x i * sb i ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun j => x j * sb j)
      (fun j _ => mul_nonneg (hx2 j) (hsb2 j).le) (Finset.mem_univ i)
    have : x ⬝ᵥ sb = ∑ j, x j * sb j := rfl
    try simp only at *
    linarith
  have hsi : ∀ i, xb i * s i ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun j => xb j * s j)
      (fun j _ => mul_nonneg (hxb2 j).le (hs2 j)) (Finset.mem_univ i)
    have : xb ⬝ᵥ s = ∑ j, xb j * s j := rfl
    try simp only at *
    linarith
  have hC0 : 0 ≤ C := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [C]
    · exact le_trans (div_nonneg hM (hsb2 ⟨0, hn⟩).le) (hC1 ⟨0, hn⟩)
  rw [Prod.norm_def, max_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg hC0]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hx2 i)]
    refine le_trans ?_ (hC1 i)
    rw [le_div_iff₀ (hsb2 i)]
    exact hxi i
  · rw [pi_norm_le_iff_of_nonneg hC0]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hs2 i)]
    refine le_trans ?_ (hC2 i)
    rw [le_div_iff₀ (hxb2 i), mul_comm]
    exact hsi i
