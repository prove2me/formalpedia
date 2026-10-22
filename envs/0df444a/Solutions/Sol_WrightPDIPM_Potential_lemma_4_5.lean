-- Prove2me | solution 1 for WrightPDIPM.Potential.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:46:23.501524+00:00
-- url     : https://prove2.me/submissions/c9869677-fc03-4a2c-834d-8814aec686e2

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix
open WrightPDIPM.Potential

open Matrix
open WrightPDIPM.Potential

theorem g70wr_core45 {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (μ : ℝ)
    (hμ0 : 0 < μ) (hμ : ∑ i, v i ^ 2 = n * μ) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n < ρ)
    (i0 : Fin n) :
    3 / 4 * ((n : ℝ) / ρ * μ) ^ 2 / (v i0) ^ 2 ≤ ∑ i, (-v i + (n : ℝ) / ρ * μ / v i) ^ 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hρ0 : 0 < ρ := by linarith
  set a := (n : ℝ) / ρ * μ with ha
  set p : Fin n → ℝ := fun i => 1 / v i - v i / μ with hp
  have hpt : ∀ i, (-v i + a / v i) ^ 2 =
      a ^ 2 * p i ^ 2 + 2 * a * (a / μ - 1) * (1 - v i ^ 2 / μ) + (a / μ - 1) ^ 2 * v i ^ 2 := by
    intro i
    have := (hv i).ne'
    simp only [hp]
    field_simp
    ring
  have hsum0 : ∑ i, (1 - v i ^ 2 / μ) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμ]
    simp
    field_simp
    ring
  have htot : ∑ i, (-v i + a / v i) ^ 2 = a ^ 2 * ∑ i, p i ^ 2 + (a / μ - 1) ^ 2 * (n * μ) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hμ]
    ring
  rw [htot]
  have hp0 : p i0 ^ 2 ≤ ∑ i, p i ^ 2 :=
    Finset.single_le_sum (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i0)
  have hρn : Real.sqrt n ≤ ρ - n := by linarith
  have hρn2 : (n : ℝ) ≤ (ρ - n) ^ 2 := by
    have := mul_le_mul hρn hρn hsq (by linarith)
    rw [Real.mul_self_sqrt hnr.le] at this
    nlinarith
  have hsecond : a ^ 2 / μ ≤ (a / μ - 1) ^ 2 * (n * μ) := by
    have e1 : a / μ - 1 = -(ρ - n) / ρ := by rw [ha]; field_simp; ring
    rw [e1, ha]
    rw [div_pow, div_le_iff₀ hμ0]
    have : ((n : ℝ) / ρ * μ) ^ 2 = n * (n * μ ^ 2 / ρ ^ 2) := by ring
    rw [this]
    have h2 : 0 ≤ n * μ ^ 2 / ρ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hρn2 h2
    calc (n : ℝ) * (n * μ ^ 2 / ρ ^ 2) ≤ (ρ - n) ^ 2 * (n * μ ^ 2 / ρ ^ 2) := this
      _ = (-(ρ - ↑n)) ^ 2 / ρ ^ 2 * (↑n * μ) * μ := by field_simp
  have hm := hv i0
  have hkey : 3 / 4 / v i0 ^ 2 ≤ p i0 ^ 2 + 1 / μ := by
    have : p i0 ^ 2 + 1 / μ - 3 / 4 / v i0 ^ 2 = (1 / (2 * v i0) - v i0 / μ) ^ 2 := by
      simp only [hp]; field_simp; ring
    nlinarith [sq_nonneg (1 / (2 * v i0) - v i0 / μ)]
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  calc 3 / 4 * a ^ 2 / v i0 ^ 2 = a ^ 2 * (3 / 4 / v i0 ^ 2) := by ring
    _ ≤ a ^ 2 * (p i0 ^ 2 + 1 / μ) := mul_le_mul_of_nonneg_left hkey ha2
    _ = a ^ 2 * p i0 ^ 2 + a ^ 2 / μ := by ring
    _ ≤ a ^ 2 * ∑ i, p i ^ 2 + (a / μ - 1) ^ 2 * (n * μ) := by
        have := mul_le_mul_of_nonneg_left hp0 ha2
        linarith


/-- **Lemma 4.5** (Wright, p. 75). For any `(x, λ, s) ∈ F°` and for `ρ > n + √n`,
`‖r‖ ≥ (√3/(2v_min)) · (nμ/ρ)` (4.28), with `v_min`, `r` from (4.20) and `μ = xᵀs/n`
(`n ≥ 1`). -/
theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n < ρ) :
    Real.sqrt 3 / (2 * vmin x s) * (n * mu x s / ρ) ≤ norm2 (rvec ρ x s) := by
  obtain ⟨hA, hd, hx, hs⟩ := hF
  have hv : ∀ i, 0 < vvec x s i := fun i => Real.sqrt_pos.mpr (mul_pos (hx i) (hs i))
  have hv2 : ∀ i, vvec x s i ^ 2 = x i * s i := fun i =>
    Real.sq_sqrt (mul_pos (hx i) (hs i)).le
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ : ∑ i, vvec x s i ^ 2 = n * mu x s := by
    simp only [hv2, mu]; field_simp; rfl
  have hμ0 : 0 < mu x s := by
    unfold mu
    apply div_pos _ hnr
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) Finset.univ_nonempty
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := vvec x s)
  have hvm : vmin x s = vvec x s i0 := by rw [vmin, hi0]
  have core := g70wr_core45 hn (vvec x s) hv (mu x s) hμ0 hμ ρ hρ i0
  apply Real.le_sqrt_of_sq_le
  rw [hvm]
  have hm := hv i0
  have e : (Real.sqrt 3 / (2 * vvec x s i0) * (n * mu x s / ρ)) ^ 2 =
      3 / 4 * ((n : ℝ) / ρ * mu x s) ^ 2 / (vvec x s i0) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    field_simp
    ring
  rw [e]
  refine core.trans (le_of_eq ?_)
  rfl


