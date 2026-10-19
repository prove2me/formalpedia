-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.spamCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:02:28.64199+00:00
-- url     : https://prove2.me/submissions/835f41ff-f451-4da4-b4df-1e67051d1a73

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
private theorem perturbation {d : ℕ} (hd : 0 < d)
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



private lemma entry_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    |A i j| ≤ entryMax A := by
  exact_mod_cast (Finset.le_sup (f := fun p : Fin d × Fin d => ‖A p.1 p.2‖₊)
    (Finset.mem_univ (i,j)))

private lemma spectral_entry_bound (A : Matrix (Fin 4) (Fin 4) ℝ) :
    specNorm A ≤ 4 * entryMax A := by
  have he : 0 ≤ entryMax A := NNReal.coe_nonneg _
  apply operator_bound A (4 * entryMax A) (by positivity)
  intro x
  have hx : ∑ j : Fin 4, (x j)^2 = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  have rows (i : Fin 4) : (∑ j : Fin 4, A i j * x j)^2 ≤
      (4 * (entryMax A)^2) * ‖x‖^2 := by
    have hc : (∑ j : Fin 4, A i j * x j)^2 ≤
        (∑ j : Fin 4, (A i j)^2) * ‖x‖^2 := by
      simpa only [hx] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) (fun j => x j)
    have hr : (∑ j : Fin 4, (A i j)^2) ≤ 4 * (entryMax A)^2 := by
      calc
        _ ≤ ∑ j : Fin 4, (entryMax A)^2 := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (entry_bound A i j)
        _ = _ := by simp
    simpa only [hx] using hc.trans (mul_le_mul_of_nonneg_right hr (sq_nonneg ‖x‖))
  have ht : ‖A.toEuclideanLin x‖^2 ≤ (4 * entryMax A)^2 * ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ ∑ i : Fin 4, (4 * (entryMax A)^2) * ‖x‖^2 :=
        Finset.sum_le_sum (fun i _ => rows i)
      _ = _ := by simp; ring
  nlinarith [norm_nonneg (A.toEuclideanLin x), norm_nonneg x,
    mul_nonneg (show 0 ≤ 4 * entryMax A by positivity) (norm_nonneg x)]

private lemma reference_input_eq : referenceInput =
    !![1,1,1,1; 0,0,1,0; 0,0,0,1; 1,-1,0,0] := by
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  ext a i
  fin_cases a <;> fin_cases i <;>
    norm_num [referenceInput,idealPreparation,pauliOrder,Stabilizer.Pauli.mat,
      pureDensity,ket,act,hadamard,phaseS,pauliX,pauliY,pauliZ,Matrix.mul_apply,Matrix.trace,Fintype.sum_bool,
      Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      ← pow_two, hs, hn] <;> nlinarith

private lemma reference_output_eq : referenceOutput = 1 := by
  ext i a
  fin_cases i <;> fin_cases a <;>
    norm_num [referenceOutput,pauliOrder,Stabilizer.Pauli.mat,pauliX,pauliY,pauliZ,Matrix.mul_apply,
      Matrix.trace,Fintype.sum_bool,Matrix.one_apply]

private lemma reference_input_unit : IsUnit referenceInput := by
  rw [reference_input_eq]
  let C : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1/2,-1/2,-1/2,1/2; 1/2,-1/2,-1/2,-1/2; 0,1,0,0; 0,0,1,0]
  have hC : (!![1,1,1,1; 0,0,1,0; 0,0,0,1; 1,-1,0,0] : Matrix (Fin 4) (Fin 4) ℝ) * C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C,Matrix.mul_apply,Fin.sum_univ_succ]
  exact IsUnit.of_mul_eq_one C hC

private lemma nearby_unit (A0 A : Matrix (Fin 4) (Fin 4) ℝ)
    (h : entryMax (A-A0) < leastSingular (by omega) A0 / 4) : IsUnit A := by
  apply (perturbation (by omega) A0 A _).1
  exact (spectral_entry_bound (A-A0)).trans_lt (by linarith)

private lemma column_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ) (h : IsUnit A) :
    (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, A.mulVec q = v) ∧
    (∀ v : Fin 4 → ℝ, A.mulVec (A⁻¹.mulVec v) = v) := by
  have hv (v : Fin 4 → ℝ) : A.mulVec (A⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp h),Matrix.one_mulVec]
  refine ⟨fun v => ⟨A⁻¹.mulVec v, hv v, ?_⟩, hv⟩
  intro q hq
  exact (Matrix.mulVec_injective_iff_isUnit.mpr h) (hq.trans (hv v).symm)

private lemma row_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ) (h : IsUnit A) :
    (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, Matrix.vecMul q A = v) ∧
    (∀ v : Fin 4 → ℝ, Matrix.vecMul (Matrix.vecMul v A⁻¹) A = v) := by
  have hv (v : Fin 4 → ℝ) : Matrix.vecMul (Matrix.vecMul v A⁻¹) A = v := by
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp h),Matrix.vecMul_one]
  refine ⟨fun v => ⟨Matrix.vecMul v A⁻¹, hv v, ?_⟩, hv⟩
  intro q hq
  exact (Matrix.vecMul_injective_iff_isUnit.mpr h) (hq.trans (hv v).symm)

theorem solution
    (rho : Fin 4 → Matrix Bool Bool ℂ) (density : ∀ i, IsDensityMatrix (rho i))
    (Q : Fin 4 → Matrix Bool Bool ℂ) (hermitian : ∀ i, (Q i).IsHermitian) :
    let Min := Matrix.of fun a i => ((pauliOrder a).mat*rho i).trace.re
    let Mout := Matrix.of fun i a => (2⁻¹ : ℝ)*((pauliOrder a).mat*Q i).trace.re
    IsUnit referenceInput ∧ IsUnit referenceOutput ∧
    (entryMax (Min-referenceInput) < leastSingular (by omega) referenceInput/4 → IsUnit Min) ∧
    (entryMax (Mout-referenceOutput) < leastSingular (by omega) referenceOutput/4 → IsUnit Mout) ∧
    (IsUnit Min →
      (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, Min.mulVec q = v) ∧
      (∀ v : Fin 4 → ℝ, Min.mulVec (Min⁻¹.mulVec v) = v)) ∧
    (IsUnit Mout →
      (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, Matrix.vecMul q Mout = v) ∧
      (∀ v : Fin 4 → ℝ, Matrix.vecMul (Matrix.vecMul v Mout⁻¹) Mout = v))  := by
  dsimp only
  exact ⟨reference_input_unit, reference_output_eq.symm ▸ isUnit_one,
    nearby_unit referenceInput _, nearby_unit referenceOutput _,
    column_coordinates _, row_coordinates _⟩

#print axioms solution
