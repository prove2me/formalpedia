-- Prove2me | solution 1 for PrimalDualLDR.RandomRecourse.claim_3_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:20:12.368201+00:00
-- url     : https://prove2.me/submissions/8065f0b0-05f8-4809-a213-648254c82c7c

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Problems

open MeasureTheory Matrix

namespace PDLDRClaim313Aux

open PrimalDualLDR.RandomRecourse

lemma q_vecMulVec {k : ℕ} (u v ξ : Fin k → ℝ) :
    ξ ⬝ᵥ (vecMulVec u v *ᵥ ξ) = (ξ ⬝ᵥ u) * (v ⬝ᵥ ξ) := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  ring

lemma q_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (ξ : Fin k → ℝ) :
    ξ ⬝ᵥ (Mᵀ *ᵥ ξ) = ξ ⬝ᵥ (M *ᵥ ξ) := dotProduct_transpose_mulVec M ξ ξ

lemma symm_swap {k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ} (hW : Wᵀ = W) (u v : Fin k → ℝ) :
    u ⬝ᵥ (W *ᵥ v) = v ⬝ᵥ (W *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hW]

lemma eq_zero_of_q {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) (hH : Hᵀ = H)
    (h : ∀ x, x ⬝ᵥ (H *ᵥ x) = 0) : H = 0 := by
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hs : Hᵀ i j = H i j := by rw [hH]
  rw [transpose_apply] at hs
  simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single, single_dotProduct,
    op_smul_eq_smul, one_smul, Matrix.col_apply] at h1 hi hj
  rw [Matrix.zero_apply]
  linarith

end PDLDRClaim313Aux

open PDLDRClaim313Aux PrimalDualLDR.RandomRecourse in
theorem solution (σ : Setting) (hσ : σ.Standing)
    (hrelint : ∃ ξ₀ ∈ σ.Xi, ∃ r : ℝ, 0 < r ∧
      ∀ ξ : Fin σ.k → ℝ, σ.e1 ⬝ᵥ ξ = 1 → dist ξ ξ₀ < r → ξ ∈ σ.Xi)
    (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (Sμ : Matrix (Fin σ.k) (Fin σ.k) ℝ) (hS : Sμ.IsSymm)
    (μ : Fin σ.m) :
    (∀ᵐ ξ ∂σ.P, ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) = σ.B μ ⬝ᵥ ξ) ↔
      σ.H X Sμ μ = 0 := by
  have hid : ∀ ξ : Fin σ.k → ℝ, ξ ⬝ᵥ (σ.H X Sμ μ *ᵥ ξ) =
      ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) - (σ.e1 ⬝ᵥ ξ) * (σ.B μ ⬝ᵥ ξ) := by
    intro ξ
    simp only [Setting.H]
    rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, sub_mulVec, sub_mulVec,
      add_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_add, ← transpose_mul, q_transpose,
      q_vecMulVec, q_vecMulVec, smul_eq_mul, dotProduct_comm ξ σ.e1, dotProduct_comm ξ (σ.B μ)]
    ring
  have hXi : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi := by
    rw [ae_iff]
    simpa [Set.compl_def] using hσ.2.2.1.2.1
  constructor
  · intro hae
    set f : (Fin σ.k → ℝ) → ℝ := fun ξ =>
      ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) - σ.B μ ⬝ᵥ ξ with hf
    have hfc : Continuous f := by
      simp only [hf, dotProduct, mulVec]
      fun_prop
    -- Step 1: the equality holds on all of the support `Ξ`.
    have hon : ∀ ξ ∈ σ.Xi, f ξ = 0 := by
      intro ξ0 hξ0
      by_contra hne
      have hopen : IsOpen {ξ : Fin σ.k → ℝ | f ξ ≠ 0} := isOpen_ne_fun hfc continuous_const
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen ξ0 hne
      have hpos := hσ.2.2.1.2.2 ξ0 hξ0 ε hε
      have hzero : σ.P {ξ | ¬ (ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) = σ.B μ ⬝ᵥ ξ)} = 0 :=
        ae_iff.mp hae
      have hle : σ.P (Metric.ball ξ0 ε) ≤
          σ.P {ξ | ¬ (ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (Sμ *ᵥ ξ) = σ.B μ ⬝ᵥ ξ)} := by
        apply measure_mono
        intro ξ hξ
        have h1 : f ξ ≠ 0 := hball hξ
        intro h2
        apply h1
        simp only [hf]
        linarith
      rw [hzero] at hle
      exact absurd (le_zero_iff.mp hle) (ne_of_gt hpos)
    have hq0 : ∀ ξ ∈ σ.Xi, ξ ⬝ᵥ (σ.H X Sμ μ *ᵥ ξ) = 0 := by
      intro ξ hξ
      rw [hid, hξ.1]
      have := hon ξ hξ
      simp only [hf] at this
      linarith
    -- Symmetry of `H`.
    have hHs : (σ.H X Sμ μ)ᵀ = σ.H X Sμ μ := by
      simp only [Setting.H, transpose_add, transpose_smul, transpose_sub, transpose_vecMulVec,
        transpose_mul, transpose_transpose, hS.eq]
      congr 2
      abel
    set H := σ.H X Sμ μ with hHdef
    obtain ⟨ξ0, hξ0, r, hr, hrel⟩ := hrelint
    set i0 : Fin σ.k := ⟨0, σ.hk⟩ with hi0
    have he1 : ∀ y : Fin σ.k → ℝ, σ.e1 ⬝ᵥ y = y i0 := by
      intro y
      simp [Setting.e1, i0]
    have hξ01 : ξ0 i0 = 1 := by rw [← he1 ξ0]; exact hξ0.1
    have hHξ0 : ξ0 ⬝ᵥ (H *ᵥ ξ0) = 0 := hq0 ξ0 hξ0
    have hexp : ∀ (t : ℝ) (d : Fin σ.k → ℝ), (ξ0 + t • d) ⬝ᵥ (H *ᵥ (ξ0 + t • d)) =
        ξ0 ⬝ᵥ (H *ᵥ ξ0) + 2 * (t * (ξ0 ⬝ᵥ (H *ᵥ d))) + (t * t) * (d ⬝ᵥ (H *ᵥ d)) := by
      intro t d
      have h2 := symm_swap hHs d ξ0
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at *
      rw [h2]; ring
    -- Step 2: directions inside the hyperplane.
    have hdir : ∀ d : Fin σ.k → ℝ, d i0 = 0 →
        ξ0 ⬝ᵥ (H *ᵥ d) = 0 ∧ d ⬝ᵥ (H *ᵥ d) = 0 := by
      intro d hd
      set δ : ℝ := r / (2 * (‖d‖ + 1)) with hδ
      have hdn : 0 ≤ ‖d‖ := norm_nonneg d
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hδd : δ * ‖d‖ < r := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have hin : ∀ t : ℝ, |t| = δ → ξ0 + t • d ∈ σ.Xi := by
        intro t ht
        apply hrel
        · rw [he1]; simp [hξ01, hd]
        · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ht]
          exact hδd
      have hp := hq0 _ (hin δ (abs_of_pos hδpos))
      have hm := hq0 _ (hin (-δ) (by rw [abs_neg, abs_of_pos hδpos]))
      rw [hexp, hHξ0] at hp hm
      have hc : (δ * δ) * (d ⬝ᵥ (H *ᵥ d)) = 0 := by linarith
      have hc' : d ⬝ᵥ (H *ᵥ d) = 0 := by
        rcases mul_eq_zero.mp hc with h | h
        · exact absurd h (ne_of_gt (mul_pos hδpos hδpos))
        · exact h
      refine ⟨?_, hc'⟩
      rw [hc'] at hp
      have : δ * (ξ0 ⬝ᵥ (H *ᵥ d)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hδpos)
      · exact h
    -- Step 3: the quadratic form of `H` vanishes identically.
    have hall : ∀ x : Fin σ.k → ℝ, x ⬝ᵥ (H *ᵥ x) = 0 := by
      intro x
      set d := x - x i0 • ξ0 with hd
      have hd0 : d i0 = 0 := by simp [hd, hξ01]
      have hx : x = ξ0 + (x i0) • d + (x i0 - 1) • ξ0 + ((1 : ℝ) - x i0) • d := by
        rw [hd]; module
      have hx' : x = (x i0) • ξ0 + (1 : ℝ) • d := by rw [hd]; module
      obtain ⟨h1, h2⟩ := hdir d hd0
      rw [hx']
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      rw [symm_swap hHs d ξ0, h1, h2, hHξ0]
      ring
    exact eq_zero_of_q H hHs hall
  · intro hH
    filter_upwards [hXi] with ξ hξ
    have := hid ξ
    rw [hH, zero_mulVec, dotProduct_zero, hξ.1] at this
    linarith
