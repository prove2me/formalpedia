-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.residual_after_step_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:39:00.679098+00:00
-- url     : https://prove2.me/submissions/e531ae72-ed82-4cbe-954b-e4072ba0b346

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq
theorem solution {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsOrthStage ψ x) (k : Fin n)
    (hxk : x k.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hxk1 : x (k.val + 1) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (b : ℝ) (hb : 0 < b) (hφ : b < ‖orthDir ψ x k‖) :
    |ψ k (x (k.val + 1))| ≤ L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2 ∧
      L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2 ≤ L / b ^ 2 * ψ k (x k.val) ^ 2 := by
  let x₀ := x k.val
  let x₁ := x (k.val + 1)
  let φ := orthDir ψ x k
  let h := x₁ - x₀
  let p0 := ψ k x₀
  have hφpos : 0 < ‖φ‖ := lt_trans hb hφ
  have hφne : ‖φ‖ ≠ 0 := hφpos.ne'
  have hstep : h = -(p0 / ‖φ‖ ^ 2) • φ := by
    change x (k.val + 1) - x k.val = _
    rw [hx k, neg_smul]
    exact sub_sub_cancel_left _ _
  by_cases hsame : x₁ = x₀
  · have hh : h = 0 := sub_eq_zero.mpr hsame
    have hz : -(p0 / ‖φ‖ ^ 2) • φ = 0 := by
      rw [← hstep, hh]
    have hcoef : p0 / ‖φ‖ ^ 2 = 0 := by
      rcases (smul_eq_zero.mp hz) with hc | hc
      · exact neg_eq_zero.mp hc
      · apply (hφne ?_).elim
        simpa using congrArg norm hc
    have hp0 : p0 = 0 := by
      field_simp [hφne] at hcoef
      simpa using hcoef
    simp [x₁, x₀, p0, φ, hsame, hp0]
  · have hL : 0 ≤ L := by
      have hdist : 0 < ‖x₀ - x₁‖ := by
        rw [norm_sub_rev]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hsame)
      have hlip := hLip k x₀ hxk x₁ hxk1
      nlinarith [norm_nonneg (gradient (ψ k) x₀ - gradient (ψ k) x₁)]
    have hinnerφ : inner ℝ (gradient (ψ k) x₀) φ = ‖φ‖ ^ 2 := by
      let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
        Submodule.span ℝ
          (Set.range fun j : Fin k.val =>
            gradient (ψ ⟨j.val, j.isLt.trans k.isLt⟩) (x j.val))
      have hmem : φ ∈ Sᗮ := by
        simpa [φ, orthDir, S] using
          (Submodule.starProjection_apply_mem Sᗮ (gradient (ψ k) x₀))
      have hz := Submodule.starProjection_inner_eq_zero
        (K := Sᗮ) (gradient (ψ k) x₀) φ hmem
      have hz' : inner ℝ (gradient (ψ k) x₀) φ - inner ℝ φ φ = 0 := by
        simpa only [φ, orthDir, S, inner_sub_left] using hz
      have hself : inner ℝ φ φ = ‖φ‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (x := φ))
      rw [hself] at hz'
      linarith
    have hinnerh : inner ℝ (gradient (ψ k) x₀) h = -p0 := by
      rw [hstep]
      simp only [inner_smul_right, hinnerφ]
      field_simp [hφne]
    have hconv := convex_ball (0 : EuclideanSpace ℝ (Fin n)) δ
    have hx0h : x₀ + h = x₁ := by
      change x₀ + (x₁ - x₀) = x₁
      abel
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        x₀ + t • h ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ := by
      intro t ht
      have : x₀ + t • h = (1 - t) • x₀ + t • x₁ := by
        rw [← hx0h]
        module
      rw [this]
      exact hconv hxk (by simpa [x₁] using hxk1) (by linarith [ht.2])
        ht.1 (by ring)
    let F : ℝ → ℝ := fun t => ψ k (x₀ + t • h) + t * p0
    have hderiv : ∀ t : ℝ,
        HasDerivAt F (inner ℝ (gradient (ψ k) (x₀ + t • h)) h + p0) t := by
      intro t
      have h1 : HasFDerivAt (ψ k) (fderiv ℝ (ψ k) (x₀ + t • h))
          (x₀ + t • h) :=
        ((hψ k).differentiable one_ne_zero _).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x₀ + t • h) h t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_add x₀
      have hcomp := h1.comp_hasDerivAt t h2
      have hgr : inner ℝ (gradient (ψ k) (x₀ + t • h)) h
          = fderiv ℝ (ψ k) (x₀ + t • h) h := by
        simp [gradient, InnerProductSpace.toDual_symm_apply]
      have hlin : HasDerivAt (fun t : ℝ => t * p0) p0 t := by
        simpa using (hasDerivAt_id t).mul_const p0
      rw [hgr]
      exact hcomp.add hlin
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖inner ℝ (gradient (ψ k) (x₀ + t • h)) h + p0‖ ≤
          L * ‖h‖ ^ 2 := by
      intro t ht
      have hlip := hLip k _ (hseg t ht) x₀ hxk
      have hdiff :
          inner ℝ (gradient (ψ k) (x₀ + t • h)) h + p0
            = inner ℝ (gradient (ψ k) (x₀ + t • h)
                - gradient (ψ k) x₀) h := by
        rw [inner_sub_left, hinnerh]
        ring
      rw [hdiff]
      refine (norm_inner_le_norm _ _).trans ?_
      have hnorm : ‖x₀ + t • h - x₀‖ = t * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
      rw [hnorm] at hlip
      calc
        ‖gradient (ψ k) (x₀ + t • h) - gradient (ψ k) x₀‖ * ‖h‖
            ≤ (L * (t * ‖h‖)) * ‖h‖ :=
              mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        _ = L * t * ‖h‖ ^ 2 := by ring
        _ = L * (t * ‖h‖ ^ 2) := by ring
        _ ≤ L * ‖h‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (sq_nonneg ‖h‖) ht.2) hL
    have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := F) (f' := fun t => inner ℝ (gradient (ψ k) (x₀ + t • h)) h + p0)
      (fun t _ => (hderiv t).hasDerivWithinAt) hbound
      (Set.left_mem_Icc.2 (by norm_num)) (Set.right_mem_Icc.2 (by norm_num))
    have hnormh : ‖h‖ ^ 2 = p0 ^ 2 / ‖φ‖ ^ 2 := by
      rw [hstep]
      simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_div,
        abs_of_nonneg (sq_nonneg ‖φ‖), abs_pow, abs_of_pos hφpos, mul_pow, sq_abs]
      field_simp [hφne]
      rw [sq_abs]
    have hfirst : |ψ k x₁| ≤ L * p0 ^ 2 / ‖φ‖ ^ 2 := by
      simpa [F, p0, hx0h, hnormh, Real.norm_eq_abs, mul_div_assoc] using key
    constructor
    · simpa [x₁, x₀, p0, φ] using hfirst
    · have hden : b ^ 2 ≤ ‖φ‖ ^ 2 := by
        nlinarith [norm_nonneg φ]
      have hratio : p0 ^ 2 / ‖φ‖ ^ 2 ≤ p0 ^ 2 / b ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg p0) (sq_pos_of_pos hb) hden
      have hmul : L * (p0 ^ 2 / ‖φ‖ ^ 2) ≤ L * (p0 ^ 2 / b ^ 2) :=
        mul_le_mul_of_nonneg_left hratio hL
      calc
        L * ψ k (x k.val) ^ 2 / ‖orthDir ψ x k‖ ^ 2
            = L * (p0 ^ 2 / ‖φ‖ ^ 2) := by simp [p0, φ]; ring
        _ ≤ L * (p0 ^ 2 / b ^ 2) := hmul
        _ = L / b ^ 2 * ψ k (x k.val) ^ 2 := by simp [p0]; ring
