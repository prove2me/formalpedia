-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.perturbationInvertibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:55:53.762292+00:00
-- url     : https://prove2.me/submissions/d9b04cde-bd47-4ec0-8361-be2fe4e45b6c

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open QAlgorithms QAlgorithms.ErrorMitigation
open QAlgorithms.Papers.Independent.Independent1.P09
open scoped Matrix.Norms.L2Operator

private lemma operator_bound {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (bound : ∀ x : EuclideanSpace ℝ (Fin d), ‖B.toEuclideanLin x‖ ≤ C * ‖x‖) :
    specNorm B ≤ C := by
  change ‖(B.toEuclideanLin).toContinuousLinearMap‖ ≤ C
  exact (B.toEuclideanLin).toContinuousLinearMap.opNorm_le_bound hC bound

private lemma least_lower {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    leastSingular hd A * ‖x‖ ≤ ‖A.toEuclideanLin x‖ := by
  let H := A.transpose * A
  have hH : H.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  let b := hH.eigenvectorBasis
  let e : Fin d ≃ Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let k : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd⟩
  let m := hH.eigenvalues₀ k.rev
  have hmin (i : Fin d) : m ≤ hH.eigenvalues i := by
    apply hH.eigenvalues₀_antitone
    change (e i).val ≤ k.rev.val
    simp only [Fin.val_rev]
    have := (e i).isLt
    dsimp [k]
    omega
  have hm : 0 ≤ m := by
    have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A (e.symm k.rev)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.IsHermitian.eigenvalues,
      H, m, e] using this
  have hs : leastSingular hd A = Real.sqrt m := by
    change Real.sqrt (ascEigenvalues H k) = Real.sqrt m
    rw [ascEigenvalues, dif_pos hH]
  have hc (i : Fin d) : b.repr (H.toEuclideanLin x) i =
      hH.eigenvalues i * b.repr x i := by
    rw [b.repr_apply_apply, b.repr_apply_apply]
    rw [← Matrix.isSymmetric_toEuclideanLin_iff.mpr hH]
    have he : H.toEuclideanLin (b i) = hH.eigenvalues i • b i := by
      apply PiLp.ext
      intro j
      exact congrFun (hH.mulVec_eigenvectorBasis i) j
    rw [he, inner_smul_left]
    simp
  have hinner : inner ℝ x (H.toEuclideanLin x) = ‖A.toEuclideanLin x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply,
      starRingEnd_apply, star_trivial, H]
    change ((A.transpose * A).mulVec x.ofLp) ⬝ᵥ x.ofLp =
      (A.mulVec x.ofLp) ⬝ᵥ (A.mulVec x.ofLp)
    rw [dotProduct_comm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : m * ‖x‖ ^ 2 ≤ inner ℝ x (H.toEuclideanLin x) := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq,
      ← b.repr.inner_map_map, PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hc, Finset.mul_sum,
      Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hmin i, sq_nonneg (b.repr x i)]
  rw [hinner] at hsum
  rw [hs]
  have hsq := Real.sq_sqrt hm
  nlinarith [norm_nonneg x, norm_nonneg (A.toEuclideanLin x),
    Real.sqrt_nonneg m, sq_nonneg (Real.sqrt m * ‖x‖ - ‖A.toEuclideanLin x‖)]

/-- Appendix C (C1)--(C3) and Appendix F (F10). -/
theorem solution {d : ℕ} (hd : 0 < d)
    (A0 A : Matrix (Fin d) (Fin d) ℝ)
    (small : specNorm (A-A0) < leastSingular hd A0) :
    IsUnit A ∧
    (∀ x : EuclideanSpace ℝ (Fin d),
      (leastSingular hd A0-specNorm (A-A0))*‖x‖ ≤
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖) ∧
    specNorm A⁻¹ ≤ (leastSingular hd A0-specNorm (A-A0))⁻¹ := by
  let c := leastSingular hd A0 - specNorm (A-A0)
  have hc : 0 < c := sub_pos.mpr small
  have lower (x : EuclideanSpace ℝ (Fin d)) : c * ‖x‖ ≤ ‖A.toEuclideanLin x‖ := by
    have h0 := least_lower hd A0 x
    have herror := (A-A0).l2_opNorm_mulVec x
    have hadd : A0.toEuclideanLin x =
        A.toEuclideanLin x - (A-A0).toEuclideanLin x := by
      simp [map_sub]
    have ht := norm_sub_le (A.toEuclideanLin x) ((A-A0).toEuclideanLin x)
    rw [← hadd] at ht
    change ‖(A-A0).toEuclideanLin x‖ ≤ specNorm (A-A0) * ‖x‖ at herror
    dsimp [c]
    linarith
  have hu : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro u v huv
    have h := lower (WithLp.toLp 2 (u-v))
    have hz : A.toEuclideanLin (WithLp.toLp 2 (u-v)) = 0 := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_sub, huv]
    rw [hz, norm_zero] at h
    have hv : WithLp.toLp 2 (u-v) = (0 : EuclideanSpace ℝ (Fin d)) := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (WithLp.toLp 2 (u-v) : EuclideanSpace ℝ (Fin d))]
    have hv' : u-v = 0 := by
      simpa using congrArg WithLp.ofLp hv
    exact sub_eq_zero.mp hv'
  refine ⟨hu, lower, ?_⟩
  apply operator_bound A⁻¹ c⁻¹ (le_of_lt (inv_pos.mpr hc))
  intro y
  have h := lower (A⁻¹.toEuclideanLin y)
  have hy : A.toEuclideanLin (A⁻¹.toEuclideanLin y) = y := by
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp hu), Matrix.one_mulVec, WithLp.toLp_ofLp]
  rw [hy] at h
  change ‖A⁻¹.toEuclideanLin y‖ ≤ c⁻¹ * ‖y‖
  calc
    ‖A⁻¹.toEuclideanLin y‖ ≤ ‖y‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)
    _ = c⁻¹ * ‖y‖ := by ring

#print axioms solution
