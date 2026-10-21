-- Prove2me | solution 1 for SparseNLO.Partial.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:19:17.5105+00:00
-- url     : https://prove2.me/submissions/0380a40f-7b2e-4d65-a781-9d331f71cabb

import Mathlib
import Definitions.Def_SparseNLO_Partial_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open SparseNLO.Partial

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (i j : Fin n) (hij : i ≠ j) (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L2 / 2 * ‖d‖ ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgrad : ∀ p w : EuclideanSpace ℝ (Fin n), fderiv ℝ f p w = ⟪gradient f p, w⟫ := by
    intro p w
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hphi : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • d)) (⟪gradient f (x + t • d), d⟫) t := by
    intro t
    have := (hdiff (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [hgrad] at this
    exact this
  have hnorm : ‖d‖ ^ 2 = d i ^ 2 + d j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_eq_add i j hij]
    · intro c _ h; simp [hd c h.1 h.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hinner : ∀ g : EuclideanSpace ℝ (Fin n), ⟪g, d⟫ = g i * d i + g j * d j := by
    intro g
    rw [PiLp.inner_apply, Finset.sum_eq_add i j hij]
    · simp [mul_comm]
    · intro c _ h; simp [hd c h.1 h.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * ⟪gradient f x, d⟫
    - L2 / 2 * ‖d‖ ^ 2 * t ^ 2 with hψ
  have hψd : ∀ t : ℝ, HasDerivAt ψ (⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫
      - L2 * ‖d‖ ^ 2 * t) t := by
    intro t
    have h1 := ((hphi t).sub_const (f x)).sub ((hasDerivAt_id t).mul_const (⟪gradient f x, d⟫))
    have h2 := h1.sub ((hasDerivAt_pow 2 t).const_mul (L2 / 2 * ‖d‖ ^ 2))
    exact h2.congr_deriv (by norm_num; ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hloc := hL2 i j hij x (t • d) (by intro k h1 h2; simp [hd k h1 h2])
      have hnt : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnt] at hloc
      set a := gradient f (x + t • d) i - gradient f x i with ha
      set b := gradient f (x + t • d) j - gradient f x j with hb
      have hs : Real.sqrt (a ^ 2 + b ^ 2) ≤ L2 * (t * ‖d‖) := by
        have : (gradient f x i - gradient f (x + t • d) i) ^ 2 + (gradient f x j - gradient f (x + t • d) j) ^ 2 = a ^ 2 + b ^ 2 := by
          simp only [ha, hb]; ring
        rw [this] at hloc
        exact hloc
      have hdd : ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ = a * d i + b * d j := by
        rw [← inner_sub_left, hinner]
        simp [ha, hb]
      rw [hdd]
      have hsq : (a * d i + b * d j) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * ‖d‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hnorm]
        nlinarith [sq_nonneg (a * d j - b * d i)]
      have hle := (abs_le_of_sq_le_sq' hsq (by positivity)).2
      have hmul : Real.sqrt (a ^ 2 + b ^ 2) * ‖d‖ ≤ L2 * (t * ‖d‖) * ‖d‖ := by gcongr
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [hψ] at h01
  simp only [zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, mul_one, sub_self] at h01
  linarith
