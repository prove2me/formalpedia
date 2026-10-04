-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.ellipsoid_method_localizes
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T20:52:23.751799+00:00
-- url     : https://prove2.me/submissions/7a043197-bc2f-4ee0-b1cf-2c23355a9806

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

-- Shared checked module: EllMethodBase
-- Geometric helper proofs adapted from Nickrobbins95’s accepted volume proof
-- 90913e48-2d1b-4258-b0a2-abc80c874c30; original source is retained and credited.

open scoped RealInnerProductSpace

open MeasureTheory

namespace ShorNonsmooth.Ellipsoid

lemma em_beta_pos {n : ℕ} (hn : 1 < n) : 0 < beta n := by
  unfold beta
  apply Real.sqrt_pos.mpr
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  apply div_pos <;> linarith

lemma em_ratio_pos {n : ℕ} (hn : 1 < n) : 0 < ratio n := by
  unfold ratio
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  apply div_pos (by linarith)
  apply Real.sqrt_pos.mpr
  nlinarith

lemma em_det_dilation {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1) :
    (dilationMatrix α ξ).det = α := by
  unfold dilationMatrix
  rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h2 : WithLp.ofLp ξ ⬝ᵥ WithLp.ofLp ξ = ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [dotProduct_smul, h2, hξ]
  simp

lemma em_direction_norm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
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

lemma em_invariant {n : ℕ} (hn : 1 < n)
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
      rw [ih2]; exact pow_ne_zero _ (em_beta_pos hn).ne'
    show (ellStep g (ellipsoidMethod g R x₀ j)).h = _ ∧ (ellStep g (ellipsoidMethod g R x₀ j)).B.det = _
    unfold ellStep
    rw [if_neg hg]
    refine ⟨?_, ?_⟩
    · simp only
      rw [ih1, pow_succ]; ring
    · simp only
      rw [Matrix.det_mul, ih2, em_det_dilation _ _ (em_direction_norm _ hdet _ hg), pow_succ]

lemma em_volume {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
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


-- Shared checked module: EllMethodGeometry

namespace ShorNonsmooth.Ellipsoid
open scoped RealInnerProductSpace
noncomputable section

lemma em_mul_apply {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (B*C) x=Matrix.toEuclideanLin B (Matrix.toEuclideanLin C x) := by
  change Matrix.toLpLin 2 2 (B*C) x=Matrix.toLpLin 2 2 B (Matrix.toLpLin 2 2 C x)
  rw [Matrix.toLpLin_mul]
  rfl

lemma em_one_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) x=x := by
  simp [Matrix.toEuclideanLin]

-- Adapted from dilation_apply_aux in Nickrobbins95's accepted dilation-norm proof.
lemma em_dilation_apply {n : ℕ} (α : ℝ) (ξ x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (dilationMatrix α ξ) x=x+((α-1)*inner ℝ x ξ) • ξ := by
  ext i
  simp only [dilationMatrix,Matrix.toEuclideanLin_apply,PiLp.add_apply,PiLp.smul_apply,
    smul_eq_mul,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Matrix.of_apply,Pi.add_apply,Pi.smul_apply,
    EuclideanSpace.inner_eq_star_dotProduct,star_trivial,PiLp.toLp_apply]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma em_dilation_norm_sq {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖=1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (dilationMatrix α ξ) x‖^2=
    ‖x‖^2+(α^2-1)*(inner ℝ x ξ)^2 := by
  rw [em_dilation_apply,@norm_add_sq_real,norm_smul,inner_smul_right,Real.norm_eq_abs,
    mul_pow,sq_abs,hξ]
  ring

lemma em_dilation_inv {n : ℕ} (α : ℝ) (hα : α≠0)
    (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖=1) :
    (dilationMatrix α ξ)⁻¹=dilationMatrix α⁻¹ ξ := by
  apply Matrix.inv_eq_right_inv
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  rw [em_mul_apply,em_one_apply]
  have hii : inner ℝ ξ ξ=1 := by rw [real_inner_self_eq_norm_sq,hξ]; norm_num
  simp only [em_dilation_apply,inner_add_left,real_inner_smul_left,hii,mul_one]
  rw [add_assoc,← add_smul]
  have he : (α⁻¹-1)*inner ℝ x ξ+(α-1)*(inner ℝ x ξ+(α⁻¹-1)*inner ℝ x ξ)=0 := by
    field_simp [hα]
    ring
  rw [he,zero_smul,add_zero]

lemma em_inv_right {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det≠0)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin B (Matrix.toEuclideanLin B⁻¹ x)=x := by
  rw [← em_mul_apply,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),em_one_apply]

lemma em_inv_left {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det≠0)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin B⁻¹ (Matrix.toEuclideanLin B x)=x := by
  rw [← em_mul_apply,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),em_one_apply]

lemma em_transpose_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanLin B.transpose v) w=inner ℝ v (Matrix.toEuclideanLin B w) := by
  have he : Matrix.toEuclideanLin B.transpose=(Matrix.toEuclideanLin B).adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint B
  rw [he,LinearMap.adjoint_inner_left]

lemma em_direction_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det≠0)
    (v z : EuclideanSpace ℝ (Fin n)) (hz : 0≤ inner ℝ v z) :
    0≤ inner ℝ (Matrix.toEuclideanLin B⁻¹ z) (direction B v) := by
  unfold direction
  rw [real_inner_smul_right,real_inner_comm,em_transpose_inner,em_inv_right B hB]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hz

lemma em_beta_sq {n : ℕ} (hn : 1<n) : (beta n)^2=((n:ℝ)-1)/((n:ℝ)+1) := by
  unfold beta
  apply Real.sq_sqrt
  have h : (1:ℝ)<n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (by positivity)

lemma em_ratio_sq {n : ℕ} (hn : 1<n) : (ratio n)^2=(n:ℝ)^2/((n:ℝ)^2-1) := by
  unfold ratio
  rw [div_pow,Real.sq_sqrt]
  have h : (1:ℝ)<n := by exact_mod_cast hn
  nlinarith

lemma em_localization_geometry {n : ℕ} (hn : 1<n) (h : ℝ) (hh : 0≤h)
    (ξ u : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖=1)
    (hu : ‖u‖≤h*((n:ℝ)+1)) (hs : 0≤ inner ℝ u ξ) :
    ‖Matrix.toEuclideanLin (dilationMatrix (beta n) ξ)⁻¹ (u-h • ξ)‖≤
      ratio n*h*((n:ℝ)+1) := by
  have hnR : (1:ℝ)<n := by exact_mod_cast hn
  have hnm : (n:ℝ)-1≠0 := by linarith
  have hn2 : (n:ℝ)^2-1≠0 := by nlinarith
  have hβ : (beta n)⁻¹^2-1=2/((n:ℝ)-1) := by
    rw [inv_pow,em_beta_sq hn,inv_div]
    field_simp [hnm]
    ring
  have hii : inner ℝ ξ ξ=1 := by rw [real_inner_self_eq_norm_sq,hξ]; norm_num
  have hi : inner ℝ (u-h • ξ) ξ=inner ℝ u ξ-h := by
    rw [inner_sub_left,real_inner_smul_left,hii,mul_one]
  have hnorm : ‖u-h • ξ‖^2=‖u‖^2-2*h*inner ℝ u ξ+h^2 := by
    rw [@norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hξ]
    ring
  have he : ‖Matrix.toEuclideanLin (dilationMatrix (beta n) ξ)⁻¹ (u-h • ξ)‖^2=
      ‖u‖^2+h^2*((n:ℝ)+1)/((n:ℝ)-1)+
      (2/((n:ℝ)-1))*inner ℝ u ξ*(inner ℝ u ξ-h*((n:ℝ)+1)) := by
    rw [em_dilation_inv _ (em_beta_pos hn).ne' ξ hξ,em_dilation_norm_sq _ ξ hξ,
      hi,hβ,hnorm]
    field_simp [hnm]
    ring
  have hsle : inner ℝ u ξ≤h*((n:ℝ)+1) := by
    have hi := real_inner_le_norm u ξ
    rw [hξ,mul_one] at hi
    exact hi.trans hu
  have hquad : (2/((n:ℝ)-1))*inner ℝ u ξ*(inner ℝ u ξ-h*((n:ℝ)+1))≤0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (div_nonneg (by norm_num) (by linarith)) hs) (by linarith)
  have hR : 0≤h*((n:ℝ)+1) := mul_nonneg hh (by positivity)
  have husq : ‖u‖^2≤(h*((n:ℝ)+1))^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hu
  have hb : (ratio n*h*((n:ℝ)+1))^2=(h*((n:ℝ)+1))^2+h^2*((n:ℝ)+1)/((n:ℝ)-1) := by
    rw [mul_pow,mul_pow,em_ratio_sq hn]
    field_simp [hnm,hn2]
    ring
  have hr : 0≤ratio n*h*((n:ℝ)+1) := mul_nonneg (mul_nonneg (em_ratio_pos hn).le hh) (by positivity)
  nlinarith [norm_nonneg (Matrix.toEuclideanLin (dilationMatrix (beta n) ξ)⁻¹ (u-h • ξ))]

lemma em_state_positive {n : ℕ} (hn : 1<n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0<R)
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    0<(ellipsoidMethod g R x₀ k).B.det ∧ 0<(ellipsoidMethod g R x₀ k).h := by
  induction k with
  | zero => simp [ellipsoidMethod]; exact div_pos hR (by positivity)
  | succ k ih =>
    change 0<(ellStep g (ellipsoidMethod g R x₀ k)).B.det ∧
      0<(ellStep g (ellipsoidMethod g R x₀ k)).h
    unfold ellStep
    split_ifs with hg
    · exact ih
    · simp only
      rw [Matrix.det_mul,em_det_dilation _ _ (em_direction_norm _ ih.1.ne' _ hg)]
      exact ⟨mul_pos ih.1 (em_beta_pos hn),mul_pos (em_ratio_pos hn) ih.2⟩

end
end ShorNonsmooth.Ellipsoid

-- Shared checked module: EllMethodComplete

namespace ShorNonsmooth.Ellipsoid
open scoped RealInnerProductSpace
noncomputable section

lemma em_localizes {n : ℕ} (hn : 1<n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0<R)
    (x₀ xstar : EuclideanSpace ℝ (Fin n))
    (hsol : ∀ x : EuclideanSpace ℝ (Fin n),0≤ inner ℝ (g x) (x-xstar))
    (hball : xstar∈Metric.closedBall x₀ R) (k : ℕ) :
    ‖Matrix.toEuclideanLin (ellipsoidMethod g R x₀ k).B⁻¹
      ((ellipsoidMethod g R x₀ k).x-xstar)‖≤
    (ellipsoidMethod g R x₀ k).h*((n:ℝ)+1) := by
  induction k with
  | zero =>
    have hp : (n:ℝ)+1≠0 := by positivity
    have hb : ‖x₀-xstar‖≤R := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hball
    simpa [ellipsoidMethod,Matrix.toEuclideanLin,hp] using hb
  | succ k ih =>
    let s := ellipsoidMethod g R x₀ k
    obtain ⟨hB,hh⟩ := em_state_positive hn g R hR x₀ k
    change ‖Matrix.toEuclideanLin (ellStep g s).B⁻¹ ((ellStep g s).x-xstar)‖≤
      (ellStep g s).h*((n:ℝ)+1)
    unfold ellStep
    split_ifs with hg
    · exact ih
    · let ξ := direction s.B (g s.x)
      let u := Matrix.toEuclideanLin s.B⁻¹ (s.x-xstar)
      have hξ : ‖ξ‖=1 := em_direction_norm s.B hB.ne' (g s.x) hg
      have hs : 0≤ inner ℝ u ξ := em_direction_inner s.B hB.ne' (g s.x) (s.x-xstar) (hsol s.x)
      have he : (s.x-s.h • Matrix.toEuclideanLin s.B ξ)-xstar=
          (s.x-xstar)-s.h • Matrix.toEuclideanLin s.B ξ := by abel
      have hemap : Matrix.toEuclideanLin s.B⁻¹
          ((s.x-s.h • Matrix.toEuclideanLin s.B ξ)-xstar)=u-s.h • ξ := by
        rw [he,map_sub,map_smul,em_inv_left s.B hB.ne']
      change ‖Matrix.toEuclideanLin (s.B*dilationMatrix (beta n) ξ)⁻¹
          ((s.x-s.h • Matrix.toEuclideanLin s.B ξ)-xstar)‖≤
        (ratio n*s.h)*((n:ℝ)+1)
      rw [Matrix.mul_inv_rev,em_mul_apply,hemap]
      exact em_localization_geometry hn s.h hh.le ξ u hξ ih hs

end
end ShorNonsmooth.Ellipsoid

open ShorNonsmooth.Ellipsoid MeasureTheory
open scoped RealInnerProductSpace

/-- Shor (1985), p. 86, Theorem 3.14. Let `n > 1`, let `g` be a vector field on `E_n` (not
necessarily continuous) and let `x*` solve the problem `(g(x), x - x*) ≥ 0` for all `x ∈ E_n`,
with `x* ∈ S(x₀, R)`, `R > 0`. Then the sequence generated by the algorithm (3.57)–(3.60)
(`B₀ = I`, `h₀ = R/(n + 1)`) satisfies `‖A_k (x_k - x*)‖ ≤ h_k (n + 1)` for all `k = 0, 1, …`,
where `A_k = B_k⁻¹` (3.61). If `g(x_k) = 0` the method stops and the state is repeated
(see `ellStep`). The book's standing assumption "`g(x) ≠ 0` if `x ≠ x*`" is not used by the
proof on pp. 86–87 and is dropped. -/
theorem solution {n : ℕ} (hn : 1 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (x₀ xstar : EuclideanSpace ℝ (Fin n))
    (hsol : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ (g x) (x - xstar))
    (hball : xstar ∈ Metric.closedBall x₀ R) (k : ℕ) :
    ‖Matrix.toEuclideanLin (ellipsoidMethod g R x₀ k).B⁻¹
        ((ellipsoidMethod g R x₀ k).x - xstar)‖ ≤
      (ellipsoidMethod g R x₀ k).h * ((n : ℝ) + 1) := by
  exact em_localizes hn g R hR x₀ xstar hsol hball k

#print axioms solution
