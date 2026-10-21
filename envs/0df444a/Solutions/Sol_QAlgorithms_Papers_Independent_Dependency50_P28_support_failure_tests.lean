-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P28.support_failure_tests
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:21:28.597863+00:00
-- url     : https://prove2.me/submissions/c07fba8f-86b8-46c9-87eb-8108a964c3b1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (projection operatorRange) in
theorem g55c_supp {K : Type} [Fintype K] [DecidableEq K] (X : Matrix K K ℂ) :
    (support X)ᴴ = support X ∧ support X * X = X ∧ ∃ Y : Matrix K K ℂ, support X = X * Y := by
  set S := operatorRange X with hS
  set P := support X with hP
  have hL : Matrix.toEuclideanLin P = S.starProjection.toLinearMap := by
    rw [hP]; unfold support projection; rw [← hS]; exact LinearEquiv.apply_symm_apply _ _
  have hPv : ∀ w : K → ℂ, P *ᵥ w = (S.starProjection (WithLp.toLp 2 w)).ofLp := by
    intro w
    have := congrArg (fun L => (L (WithLp.toLp 2 w)).ofLp) hL
    simpa [Matrix.toEuclideanLin_apply] using this
  have hmem : ∀ w : K → ℂ, WithLp.toLp 2 (X *ᵥ w) ∈ S := by
    intro w; rw [hS]; exact ⟨WithLp.toLp 2 w, by simp [Matrix.toEuclideanLin_apply]⟩
  refine ⟨?_, ?_, ?_⟩
  · have hsym : (Matrix.toEuclideanLin P).IsSymmetric := by
      rw [hL]; exact S.starProjection_isSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mp hsym
  · apply Matrix.toLin'.injective
    apply LinearMap.ext; intro w
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    rw [hPv, Submodule.starProjection_eq_self_iff.mpr (hmem w)]
  · have hcol : ∀ j : K, ∃ y : K → ℂ, X *ᵥ y = P *ᵥ Pi.single j 1 := by
      intro j
      have h1 : S.starProjection (WithLp.toLp 2 (Pi.single j 1)) ∈ S := S.starProjection_apply_mem _
      rw [hS] at h1
      obtain ⟨y, hy⟩ := h1
      refine ⟨y.ofLp, ?_⟩
      rw [hPv, ← hy]; simp [Matrix.toEuclideanLin_apply]
    choose y hy using hcol
    refine ⟨Matrix.of fun i j => y j i, ?_⟩
    ext i j
    have := congrFun (hy j) i
    rw [Matrix.mulVec_single_one] at this
    rw [show P i j = (X *ᵥ y j) i by rw [this]; rfl]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem g55c_proj_unique {K : Type} [Fintype K] [DecidableEq K] (X P Q Y Z : Matrix K K ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hPX : P * X = X) (hQX : Q * X = X) (hY : P = X * Y) (hZ : Q = X * Z) :
    P = Q := by
  have h1 : Q * P = P := by rw [hY, ← Matrix.mul_assoc, hQX]
  have h2 : P * Q = Q := by rw [hZ, ← Matrix.mul_assoc, hPX]
  calc P = Pᴴ := hP.symm
    _ = (Q * P)ᴴ := by rw [h1]
    _ = P * Q := by rw [Matrix.conjTranspose_mul, hP, hQ]
    _ = Q := h2

theorem g55c_copies_mul {K : Type} [Fintype K] (m : ℕ) (A B : Matrix K K ℂ) :
    copies m (A * B) = copies m A * copies m B := by
  ext x y
  simp only [copies, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun z => ?_
  rw [Finset.prod_mul_distrib]

theorem g55c_copies_ct {K : Type} [Fintype K] (m : ℕ) (A : Matrix K K ℂ) :
    (copies m A)ᴴ = copies m Aᴴ := by
  ext x y
  show star (∏ i, A (y i) (x i)) = ∏ i, star (A (y i) (x i))
  rw [Complex.star_def, map_prod]

theorem g55c_copies_trace {K : Type} [Fintype K] (m : ℕ) (A : Matrix K K ℂ) :
    (copies m A).trace = A.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, copies, Matrix.of_apply]
  rw [show (∑ i, A i i) ^ m = ∏ _i : Fin m, ∑ j, A j j by simp, Fintype.prod_sum]

theorem g55c_supp_copies {K : Type} [Fintype K] [DecidableEq K] (m : ℕ) (X : Matrix K K ℂ) :
    support (copies m X) = copies m (support X) := by
  obtain ⟨h1, h2, Y, h3⟩ := g55c_supp X
  obtain ⟨k1, k2, Z, k3⟩ := g55c_supp (copies m X)
  refine g55c_proj_unique (copies m X) _ _ Z (copies m Y) k1 ?_ k2 ?_ k3 ?_
  · rw [g55c_copies_ct, h1]
  · rw [← g55c_copies_mul, h2]
  · rw [← g55c_copies_mul, ← h3]

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.10: Support failure admits exponentially successful zero-beta tests. Extended log includes c=0, giving alpha_n=0 and exponent +infinity. No unequal-state or support-inclusion premise from later subsections is imported. -/
theorem solution (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : ¬ SupportLE rho sigma) :
    (∀ n : ℕ, 1 ≤ n →
      let T : Mat (Fin n → I) := 1 - support (copies n sigma)
      IsEffect T ∧ accept sigma n T = 0 ∧
      (∀ r : ℝ, 0 < r → accept sigma n T ≤ Real.exp (-(n : ℝ) * r)) ∧
      typeI rho n T = (tr (rho * support sigma)) ^ n) ∧
    0 < -logNonnegativeExtended (tr (rho * support sigma)) ∧
    Tendsto (fun n => scaled n (logNonnegativeExtended (typeI rho (n + 1) (1 - support (copies (n + 1) sigma)))))
      atTop (nhds (logNonnegativeExtended (tr (rho * support sigma)))) := by
  obtain ⟨hP1, hP2, Y, hP3⟩ := g55c_supp sigma
  set P := support sigma with hPdef
  have hsH : sigmaᴴ = sigma := hsigma.1.isHermitian
  have hrH : rhoᴴ = rho := hrho.1.isHermitian
  have hσP : sigma * P = sigma := by
    have := congrArg Matrix.conjTranspose hP2
    rwa [Matrix.conjTranspose_mul, hP1, hsH] at this
  have hPP : P * P = P := by
    have : P * P = P * sigma * Y := by rw [Matrix.mul_assoc, ← hP3]
    rw [this, hP2, ← hP3]
  set c := tr (rho * P) with hc
  have hcz : (rho * P).trace = (c : ℂ) := by
    have hconj : star ((rho * P).trace) = (rho * P).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP1, hrH, Matrix.trace_mul_comm]
    apply Complex.ext
    · simp [hc, tr]
    · have := congrArg Complex.im hconj
      simp only [Complex.star_def, Complex.conj_im] at this
      simp; linarith
  have hc0 : 0 ≤ c := by
    have h1 : (rho * P).trace = (Pᴴ * rho * P).trace := by
      rw [hP1, Matrix.trace_mul_cycle, hPP, Matrix.trace_mul_comm]
    have h2 := (hrho.1.conjTranspose_mul_mul_same P).trace_nonneg
    rw [← h1] at h2
    have := (Complex.le_def.mp h2).1
    simpa [hc, tr] using this
  have htype : ∀ n : ℕ, typeI rho n (1 - support (copies n sigma)) = c ^ n := by
    intro n
    unfold typeI tr
    rw [sub_sub_cancel, g55c_supp_copies, ← g55c_copies_mul, g55c_copies_trace, hcz,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨?_, ?_, ?_⟩
  · intro n _
    intro T
    have hS : support (copies n sigma) = copies n P := g55c_supp_copies n sigma
    have hT : T = 1 - copies n P := by simp only [T, hS]
    have hSH : (copies n P)ᴴ = copies n P := by rw [g55c_copies_ct, hP1]
    have hSS : copies n P * copies n P = copies n P := by rw [← g55c_copies_mul, hPP]
    have hacc : accept sigma n T = 0 := by
      unfold accept tr
      rw [hT, Matrix.mul_sub, ← g55c_copies_mul, hσP, Matrix.mul_one, sub_self]
      simp
    refine ⟨⟨?_, ?_⟩, hacc, fun r _ => by rw [hacc]; exact (Real.exp_pos _).le, htype n⟩
    · have hTH : Tᴴ = T := by
        rw [hT, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hSH]
      have hTT : T * T = T := by
        rw [hT, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul, hSS]
        abel
      have : T = Tᴴ * T := by rw [hTH, hTT]
      rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
    · rw [hT, sub_sub_cancel]
      have : copies n P = (copies n P)ᴴ * copies n P := by rw [hSH, hSS]
      rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  · -- c < 1
    have hlt : c < 1 := by
      by_contra hge
      push Not at hge
      set Q : Matrix I I ℂ := 1 - P with hQ
      have hQH : Qᴴ = Q := by rw [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP1]
      have hQQ : Q * Q = Q := by
        rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul, hPP]
        abel
      have hpsd := hrho.1.conjTranspose_mul_mul_same Q
      have htrQ : (Qᴴ * rho * Q).trace = 1 - (c : ℂ) := by
        rw [hQH, Matrix.trace_mul_cycle, hQQ, Matrix.trace_mul_comm, hQ, Matrix.mul_sub,
          Matrix.mul_one, Matrix.trace_sub, hrho.2, hcz]
      have hz : (Qᴴ * rho * Q).trace = 0 := by
        have h2 := hpsd.trace_nonneg
        rw [htrQ] at h2 ⊢
        have := (Complex.le_def.mp h2).1
        simp at this
        have hc1 : c = 1 := le_antisymm this hge
        rw [hc1]; simp
      have h0 := (hpsd.trace_eq_zero_iff).mp hz
      obtain ⟨v, hv1, hv2⟩ := SetLike.not_le_iff_exists.mp hsupp
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv1 hv2
      have hPv : P *ᵥ v = 0 := by
        have : P = Yᴴ * sigma := by
          conv_lhs => rw [← hP1, hP3]
          rw [Matrix.conjTranspose_mul, hsH]
        rw [this, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]
      have hQv : Q *ᵥ v = v := by
        rw [hQ, Matrix.sub_mulVec, hPv, Matrix.one_mulVec, sub_zero]
      have hq : star v ⬝ᵥ rho *ᵥ v = 0 := by
        have : star v ⬝ᵥ (Qᴴ * rho * Q) *ᵥ v = 0 := by rw [h0]; simp
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          ← Matrix.star_mulVec, hQv] at this
        exact this
      exact hv2 ((hrho.1.dotProduct_mulVec_zero_iff v).mp hq)
    unfold logNonnegativeExtended
    split_ifs with hpos
    · rw [← EReal.coe_neg]
      exact EReal.coe_lt_coe_iff.mpr (by linarith [Real.log_neg hpos hlt])
    · simp
  · have hconst : ∀ n : ℕ, scaled n (logNonnegativeExtended
        (typeI rho (n + 1) (1 - support (copies (n + 1) sigma)))) = logNonnegativeExtended c := by
      intro n
      rw [htype (n + 1)]
      unfold scaled logNonnegativeExtended
      rcases hc0.lt_or_eq with hpos | hzero
      · rw [if_pos (pow_pos hpos _), if_pos hpos, Real.log_pow, ← EReal.coe_mul]
        congr 1
        push_cast
        field_simp
      · rw [← hzero]
        simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
          zero_pow, lt_self_iff_false, if_false]
        exact EReal.coe_mul_bot_of_pos (by positivity)
    simp_rw [hconst]
    exact tendsto_const_nhds


end

