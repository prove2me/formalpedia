-- Prove2me | solution 1 for SparseNLO.CWOpt.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:17:12.115352+00:00
-- url     : https://prove2.me/submissions/291e6a09-4f73-447a-9c2d-add7fd8b74cc

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

open SparseNLO.CWOpt
open scoped RealInnerProductSpace

private lemma pair_sq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ‖EuclideanSpace.single i a + EuclideanSpace.single j b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, hij, hij.symm, Real.norm_eq_abs]

private lemma pair_norm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ‖EuclideanSpace.single i a + EuclideanSpace.single j b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← pair_sq i j hij a b, Real.sqrt_sq (norm_nonneg _)]

private lemma support_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    d = EuclideanSpace.single i (d i) + EuclideanSpace.single j (d j) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [PiLp.single_apply, hij, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [PiLp.single_apply, hij, hij.symm]
    · simp [PiLp.single_apply, hki, hkj, hd k hki hkj]

private lemma local_nonneg {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL : LocalLipschitz f L) (i j : Fin n) (hij : i ≠ j) : 0 ≤ L := by
  have hh := hL i j hij 0 (EuclideanSpace.single i 1) (by
    intro k hki hkj
    simp [PiLp.single_apply, hki])
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one] at hh
  exact (Real.sqrt_nonneg _).trans hh

private lemma along_deriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (x + u • d)) ⟪gradient f (x + t • d), d⟫ t := by
  convert! (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const d).const_add x) using 1
  simp [inner_gradient_left]

private lemma along_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : ℝ) (hL : LocalLipschitz f L) (i j : Fin n) (hij : i ≠ j)
    (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) (t : ℝ) (ht : 0 ≤ t) :
    ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ ≤ L * t * ‖d‖ ^ 2 := by
  let a := gradient f x i - gradient f (x + t • d) i
  let b := gradient f x j - gradient f (x + t • d) j
  let w := EuclideanSpace.single i a + EuclideanSpace.single j b
  have hnorm : ‖w‖ ≤ L * t * ‖d‖ := by
    have hh := hL i j hij x (t • d) (by
      intro k hki hkj
      simp [hd k hki hkj])
    simpa [w, a, b, pair_norm i j hij, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, mul_assoc] using hh
  have hinner : ⟪w, d⟫ = ⟪gradient f x, d⟫ - ⟪gradient f (x + t • d), d⟫ := by
    have hg (g : EuclideanSpace ℝ (Fin n)) : ⟪g, d⟫ = d i * g i + d j * g j := by
      conv_lhs => rw [support_pair i j hij d hd]
      simp only [inner_add_right, EuclideanSpace.inner_single_right, conj_trivial]
    rw [hg (gradient f x), hg (gradient f (x + t • d))]
    simp only [w, a, b, inner_add_left, EuclideanSpace.inner_single_left, conj_trivial]
    ring
  have hh := (neg_le_abs ⟪w, d⟫).trans (abs_real_inner_le_norm w d)
  rw [hinner] at hh
  have hmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
  nlinarith

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (i j : Fin n) (hij : i ≠ j) (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L2 / 2 * ‖d‖ ^ 2 := by
  let q : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪gradient f x, d⟫ -
    L2 / 2 * t ^ 2 * ‖d‖ ^ 2
  let q' : ℝ → ℝ := fun t => ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ -
    L2 * t * ‖d‖ ^ 2
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    convert! (along_deriv f hf x d t).sub ((hasDerivAt_id t).mul_const ⟪gradient f x, d⟫) |>.sub
      ((((hasDerivAt_id t).pow 2).const_mul (L2 / 2)).mul_const (‖d‖ ^ 2)) using 1 <;>
      simp only [q, q', id_eq] <;> ring
  have hanti : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt)).continuousOn
    · intro t ht
      exact (hq t).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (interior_subset ht).1
      have hh := along_bound f L2 hL2 i j hij x d hd t ht0
      dsimp [q']
      linarith
  have hh := hanti (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) zero_le_one
  dsimp [q] at hh
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_mul, one_pow,
    zero_pow (by omega : 2 ≠ 0), mul_one, mul_zero, sub_zero] at hh
  linarith
