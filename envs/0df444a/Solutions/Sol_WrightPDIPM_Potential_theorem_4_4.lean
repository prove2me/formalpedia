-- Prove2me | solution 1 for WrightPDIPM.Potential.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:41:09.169699+00:00
-- url     : https://prove2.me/submissions/1da93ebc-629d-4838-8cca-d5d7111a3ffe

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
open Matrix
open WrightPDIPM.Potential

theorem g69b_phin_eq {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) :
    0 < mu x s ∧ Phi (n : ℝ) x s - (n : ℝ) * Real.log n =
      ∑ i, (x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hxs : 0 < x ⬝ᵥ s := by
    unfold dotProduct
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmu : 0 < mu x s := div_pos hxs hn'
  refine ⟨hmu, ?_⟩
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have e1 : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have e2 : ∑ i, x i * s i = x ⬝ᵥ s := rfl
  rw [e2, e1]
  simp_rw [Real.log_div (hw _).ne' hmu.ne']
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Phi
  rw [e1, Real.log_mul hn'.ne' hmu.ne']
  field_simp
  ring

theorem g69b_phi_lower {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) (ρ : ℝ) (hρ : (n : ℝ) < ρ) :
    0 < mu x s ∧ (ρ - n) * Real.log (mu x s) ≤ Phi ρ x s := by
  obtain ⟨hmu, he⟩ := g69b_phin_eq hn x s hx hs
  refine ⟨hmu, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ i, 0 ≤ x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s) := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (mul_pos (hx i) (hs i)) hmu)
    linarith
  have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hd i)
  have e1 : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
  have hsplit : Phi ρ x s = Phi (n : ℝ) x s + (ρ - n) * Real.log (x ⬝ᵥ s) := by
    unfold Phi; ring
  rw [hsplit, e1, Real.log_mul hn'.ne' hmu.ne']
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have : 0 ≤ (ρ - n) * Real.log n := mul_nonneg (by linarith) hlogn
  have : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn'.le hlogn
  nlinarith

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (hF : ∀ k, (x k, lam k, s k) ∈ Fo A b c)
    (δ : ℝ) (hδ : 0 < δ)
    (hdec : ∀ k, Phi ρ (x (k + 1)) (s (k + 1)) ≤ Phi ρ (x k) (s k) - δ)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ k : ℕ, ⌈Phi ρ (x 0) (s 0) / δ + (ρ - n) / δ * |Real.log ε|⌉ ≤ (k : ℤ) →
      mu (x k) (s k) ≤ ε := by
  intro k hk
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [mu]; exact hε0.le
  have hind : ∀ j : ℕ, Phi ρ (x j) (s j) ≤ Phi ρ (x 0) (s 0) - j * δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => have := hdec j; push_cast; linarith
  have hK := Int.ceil_le.mp hk
  push_cast at hK
  have hρn : 0 < ρ - n := by linarith
  have h1 : Phi ρ (x 0) (s 0) + (ρ - n) * |Real.log ε| ≤ k * δ := by
    have := mul_le_mul_of_nonneg_right hK hδ.le
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', mul_comm ((ρ - n) / δ), mul_assoc,
      div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  obtain ⟨hF1, hF2, hx, hs⟩ := hF k
  obtain ⟨hmu, hlow⟩ := g69b_phi_lower hn (x k) (s k) hx hs ρ hρ
  have hj := hind k
  have hlogε : Real.log ε < 0 := Real.log_neg hε0 hε1
  rw [abs_of_neg hlogε] at h1
  have : (ρ - n) * Real.log (mu (x k) (s k)) ≤ (ρ - n) * Real.log ε := by linarith
  have hl : Real.log (mu (x k) (s k)) ≤ Real.log ε := le_of_mul_le_mul_left this hρn
  exact (Real.log_le_log_iff hmu hε0).mp hl
