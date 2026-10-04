-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.ellipsoid_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:59:12.670988+00:00
-- url     : https://prove2.me/submissions/90913e48-2d1b-4258-b0a2-abc80c874c30

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

set_option autoImplicit false

open MeasureTheory

namespace ShorNonsmooth.Ellipsoid

lemma ab376_beta_pos {n : ℕ} (hn : 1 < n) : 0 < beta n := by
  unfold beta
  apply Real.sqrt_pos.mpr
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  apply div_pos <;> linarith

lemma ab376_ratio_pos {n : ℕ} (hn : 1 < n) : 0 < ratio n := by
  unfold ratio
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  apply div_pos (by linarith)
  apply Real.sqrt_pos.mpr
  nlinarith

lemma ab376_det_dilation {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1) :
    (dilationMatrix α ξ).det = α := by
  unfold dilationMatrix
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h2 : WithLp.ofLp ξ ⬝ᵥ WithLp.ofLp ξ = ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [dotProduct_smul, h2, hξ]
  simp

lemma ab376_direction_norm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) : ‖direction B v‖ = 1 := by
  unfold direction
  have hw : Matrix.toEuclideanLin B.transpose v ≠ 0 := by
    intro h
    apply hv
    have h' : Matrix.mulVec B.transpose (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp h
      simpa using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) h'
    simpa using congrArg (WithLp.toLp 2) this
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)

lemma ab376_invariant {n : ℕ} (hn : 1 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hrun : ∀ j < k, g (ellipsoidMethod g R x₀ j).x ≠ 0) :
    ∀ j ≤ k, (ellipsoidMethod g R x₀ j).h = R / ((n : ℝ) + 1) * ratio n ^ j ∧
      (ellipsoidMethod g R x₀ j).B.det = beta n ^ j := by
  intro j
  induction j with
  | zero => intro _; simp [ellipsoidMethod]
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hg := hrun j (by omega)
    have hdet : (ellipsoidMethod g R x₀ j).B.det ≠ 0 := by
      rw [ih2]; exact pow_ne_zero _ (ab376_beta_pos hn).ne'
    show (ellStep g (ellipsoidMethod g R x₀ j)).h = _ ∧ (ellStep g (ellipsoidMethod g R x₀ j)).B.det = _
    unfold ellStep
    rw [if_neg hg]
    refine ⟨?_, ?_⟩
    · simp only
      rw [ih1, pow_succ]; ring
    · simp only
      rw [Matrix.det_mul, ih2, ab376_det_dilation _ _ (ab376_direction_norm _ hdet _ hg), pow_succ]

lemma ab376_volume {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (ellipsoid A c ρ) = ENNReal.ofReal |A.det⁻¹| *
      (ENNReal.ofReal (ρ ^ n) * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  have hset : ellipsoid A c ρ = (fun x => x + (-c)) ⁻¹'
      ((Matrix.toEuclideanLin A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ⁻¹'
        Metric.closedBall 0 ρ) := by
    ext x
    simp [ellipsoid, sub_eq_add_neg]
  have hdet : LinearMap.det
      (Matrix.toEuclideanLin A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = A.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  rw [hset, measure_preimage_add_right, Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact hA),
    hdet, Measure.addHaar_closedBall' _ _ hρ, finrank_euclideanSpace_fin]

end ShorNonsmooth.Ellipsoid

open ShorNonsmooth.Ellipsoid MeasureTheory in
theorem solution {n : ℕ} (hn : 1 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hrun : ∀ j < k, g (ellipsoidMethod g R x₀ j).x ≠ 0) :
    ((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h = R * ratio n ^ k ∧
    ∀ c : EuclideanSpace ℝ (Fin n),
      volume (ellipsoid (ellipsoidMethod g R x₀ k).B⁻¹ c
          (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h)) =
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) *
          ENNReal.ofReal (R ^ n * ratio n ^ (n * k) / ((ellipsoidMethod g R x₀ k).B⁻¹).det) := by
  obtain ⟨h1, h2⟩ := ab376_invariant hn g R x₀ k hrun k le_rfl
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh : ((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h = R * ratio n ^ k := by
    rw [h1]; field_simp
  refine ⟨hh, ?_⟩
  intro c
  have hb : 0 < beta n ^ k := pow_pos (ab376_beta_pos hn) k
  have hr : 0 < ratio n := ab376_ratio_pos hn
  have hdetinv : ((ellipsoidMethod g R x₀ k).B⁻¹).det = (beta n ^ k)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2]
  rw [hh, ab376_volume _ (by rw [hdetinv]; exact (inv_pos.mpr hb).ne') c _ (by positivity),
    hdetinv, inv_inv, abs_of_pos hb, ← mul_assoc, ← ENNReal.ofReal_mul hb.le, mul_comm]
  congr 2
  rw [div_inv_eq_mul, mul_pow, ← pow_mul, mul_comm k n]
  ring
