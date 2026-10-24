-- Prove2me | solution 1 for SubsetShrink.L2.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:09:01.275135+00:00
-- url     : https://prove2.me/submissions/c52b8a56-363b-48fa-9e50-3cbfd5bca72c

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model
import Theorems.Thm_SubsetShrink_L2_eq_30_31
import Theorems.Thm_SubsetShrink_L2_eq_32_33
import Theorems.Thm_SubsetShrink_L2_eq_34
import Theorems.Thm_SubsetShrink_L2_g_display
import Theorems.Thm_SubsetShrink_L2_gamma_display

open SubsetShrink.L2

/-- Algebra for the slow rate on `F`, case (33): two uses of (34). -/
theorem SSL2_alg_A2 (a b L K t : ℝ) (hK2 : K ^ 2 ≤ 30) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (h : a ^ 2 ≤ b ^ 2 + L + 2 * K * t * (a + b)) :
    a ^ 2 ≤ 180 * (b ^ 2 + L + t ^ 2) := by
  have h1 := eq_34 (1 / 2) a (K * t) (by norm_num)
  have h2 := eq_34 1 b (K * t) (by norm_num)
  have h3 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg t)
  norm_num at h1 h2
  nlinarith

/-- Algebra for the fast rate: from `a² ≤ b² + 2r(a+b) + g(a+b)` derive
`a² ≤ 3b² + 16r² + 4g²`, by (34). -/
theorem SSL2_alg_B (a b r g : ℝ)
    (h : a ^ 2 ≤ b ^ 2 + 2 * r * (a + b) + g * (a + b)) :
    a ^ 2 ≤ 3 * b ^ 2 + 16 * r ^ 2 + 4 * g ^ 2 := by
  have h1 := eq_34 (1 / 2) a (2 * r + g) (by norm_num)
  have h2 := eq_34 (1 / 2) b (2 * r + g) (by norm_num)
  norm_num at h1 h2
  nlinarith [sq_nonneg (2 * r - g)]

theorem solution :
    (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p →
      (8 + 2 * Real.sqrt 2) * σ *
        Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam →
      ε ∈ E X σ (2 * k) →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤ l2 (resid X fstar β) ^ 2 + 2 * lam * l2 β) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ δ0 : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p → 0 < δ0 → δ0 ≤ 1 →
      (8 + 2 * Real.sqrt 2) * σ *
        Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam →
      ε ∈ F X σ δ0 →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤
          C * (l2 (resid X fstar β) ^ 2 + lam * l2 β + σ ^ 2 * Real.log (1 / δ0))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ δ0 : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p → 0 < δ0 → δ0 ≤ 1 → 0 ≤ lam →
      (0 < gam X (2 * k) ∨ lam = 0) →
      ε ∈ G X σ δ0 (2 * k) →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤
          C * (l2 (resid X fstar β) ^ 2 +
            σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) +
            lam ^ 2 / gam X (2 * k) ^ 2 + σ ^ 2 * Real.log (1 / δ0))) := by
  refine ⟨?_, ⟨180, by norm_num, ?_⟩, ⟨160, by norm_num, ?_⟩⟩
  · intro n p X fstar ε σ k lam βhat hX hσ hk hkp hlam hE hbest β hβ
    exact (eq_30_31 X fstar ε σ k lam βhat β hX hσ hk hkp hlam hE hbest hβ).2
  · intro n p X fstar ε σ δ0 k lam βhat hX hσ hk hkp hδ0 hδ1 hlam hF hbest β hβ
    obtain ⟨hd, h31, h33⟩ :=
      eq_32_33 X fstar ε σ δ0 k lam βhat β hX hσ hk hkp hδ0 hδ1 hlam hF hbest hβ
    have hlam0 : 0 ≤ lam := le_trans (by positivity) hlam
    have hL : 0 ≤ lam * l2 β := mul_nonneg hlam0 (Real.sqrt_nonneg _)
    have hb : 0 ≤ l2 (resid X fstar β) := Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log (1 / δ0) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have hσlog : 0 ≤ σ ^ 2 * Real.log (1 / δ0) := mul_nonneg (sq_nonneg σ) hlog
    have ht2 : (σ * Real.sqrt (Real.log (1 / δ0))) ^ 2 = σ ^ 2 * Real.log (1 / δ0) := by
      rw [mul_pow, Real.sq_sqrt hlog]
    have hK2 : (4 + Real.sqrt 2) ^ 2 ≤ 30 := by
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h15 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg 2]
    rcases hd with h | h
    · have := h31 h
      nlinarith [sq_nonneg (l2 (resid X fstar β))]
    · have h' := h33 h
      have := SSL2_alg_A2 (l2 (resid X fstar βhat)) (l2 (resid X fstar β)) (lam * l2 β)
        (4 + Real.sqrt 2) (σ * Real.sqrt (Real.log (1 / δ0))) hK2 hb hL (by linarith)
      rw [ht2] at this
      exact this
  · intro n p X fstar ε σ δ0 k lam βhat hX hσ hk hkp hδ0 hδ1 hlam hγ hG hbest β hβ
    have hg := g_display X fstar ε σ δ0 k lam βhat β hX hσ hk hkp hδ0 hδ1 hlam hG hbest hβ
    set a := l2 (resid X fstar βhat) with ha
    set b := l2 (resid X fstar β) with hb
    set γ := gam X (2 * k) with hγdef
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hkp' : (k : ℝ) ≤ p := by exact_mod_cast hkp
    have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hlog2 : 0 ≤ Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog12 : Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) ≤
        Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) hk0
      linarith
    have hlogδ : 0 ≤ Real.log (1 / δ0) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    set R := 10 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) +
      Real.log (1 / δ0) with hR
    have hR0 : 0 ≤ R := by positivity
    set r := σ * Real.sqrt R with hr
    have hr2 : r ^ 2 = σ ^ 2 * R := by rw [hr, mul_pow, Real.sq_sqrt hR0]
    -- the shrinkage term
    obtain ⟨g, hg0, hgle, hg2⟩ : ∃ g : ℝ, 0 ≤ g ∧ lam * l2 (β - βhat) ≤ g * (a + b) ∧
        g ^ 2 ≤ lam ^ 2 / γ ^ 2 := by
      rcases hγ with hγ | hγ
      · refine ⟨γ⁻¹ * lam, by positivity, ?_, le_of_eq (by field_simp)⟩
        have := gamma_display X fstar k lam βhat β hγ hlam hbest.1 hβ
        linarith [this.1, this.2]
      · refine ⟨0, le_refl _, ?_, ?_⟩
        · rw [hγ]; simp
        · rw [hγ]; simp
    have hmain := SSL2_alg_B a b r g (by
      have : 2 * σ * Real.sqrt R * (a + b) = 2 * r * (a + b) := by rw [hr]; ring
      linarith)
    have hσk : 0 ≤ σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) := by
      have : 0 ≤ Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) := le_trans hlog2 hlog12
      positivity
    have hlg : 0 ≤ lam ^ 2 / γ ^ 2 := by positivity
    have hRle : σ ^ 2 * R ≤ 10 * (σ ^ 2 * (k : ℝ) *
        Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) + σ ^ 2 * Real.log (1 / δ0) := by
      rw [hR]
      have h1 : (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) ≤
          (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog12 hk0.le
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg σ)
      nlinarith
    have hσδ : 0 ≤ σ ^ 2 * Real.log (1 / δ0) := mul_nonneg (sq_nonneg σ) hlogδ
    nlinarith [sq_nonneg b]
