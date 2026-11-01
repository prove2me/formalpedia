-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P12.reflectionApproximation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T11:12:32.008357+00:00
-- url     : https://prove2.me/submissions/910efd51-a877-41d1-a3e2-c055ccf29baf

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators Matrix ComplexConjugate
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

noncomputable section

/-! ### Part 1: Frobenius norm, unitary invariance, and Householder reflection Lipschitz bound -/

theorem g64r_frob {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    frobNorm X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  unfold frobNorm
  rw [@Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Real.rpow_two, Complex.sq_norm]

theorem g64r_nsq {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    ‖ψ‖ ^ 2 = ∑ i, Complex.normSq (ψ i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => Complex.sq_norm _)

theorem g64r_main {ι : Type*} [Fintype ι] [DecidableEq ι] (psi phi : EuclideanSpace ℂ ι)
    (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    frobNorm (householderReflection psi - householderReflection phi) ≤ 2 * Real.sqrt 2 * ‖psi - phi‖ := by
  have nψ : ∑ i, Complex.normSq (psi i) = 1 := by rw [← g64r_nsq, hpsi]; norm_num
  have nφ : ∑ i, Complex.normSq (phi i) = 1 := by rw [← g64r_nsq, hphi]; norm_num
  set d : ℂ := ∑ i, phi i * (starRingEnd ℂ) (psi i) with hd
  have hS : ∑ i, ∑ j, Complex.normSq ((householderReflection psi - householderReflection phi) i j) =
      4 * (2 - 2 * Complex.normSq d) := by
    have e : ∀ i j, (householderReflection psi - householderReflection phi) i j =
        2 * (phi i * (starRingEnd ℂ) (phi j) - psi i * (starRingEnd ℂ) (psi j)) := by
      intro i j; simp [householderReflection]; ring
    simp only [e, Complex.normSq_sub, map_mul, Complex.normSq_conj]
    have h4 : Complex.normSq 2 = 4 := by norm_num [Complex.normSq_apply]
    rw [h4]
    have hcross : ∑ i, ∑ j, (phi i * (starRingEnd ℂ) (phi j) * (starRingEnd ℂ) (psi i * (starRingEnd ℂ) (psi j))).re
        = Complex.normSq d := by
      have : Complex.normSq d = (d * (starRingEnd ℂ) d).re := by
        rw [Complex.mul_conj]; simp
      rw [this, hd, map_sum, Finset.sum_mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [map_mul, Complex.conj_conj]; ring_nf
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [map_mul] at hcross
    rw [hcross, nψ, nφ]; ring
  have hD : ‖psi - phi‖ ^ 2 = 2 - 2 * d.re := by
    rw [g64r_nsq]
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Complex.normSq_sub, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, nψ, nφ, ← Finset.mul_sum, ← Complex.re_sum]
    have : ∑ i, psi i * (starRingEnd ℂ) (phi i) = (starRingEnd ℂ) d := by
      rw [hd, map_sum]; refine Finset.sum_congr rfl fun i _ => ?_; simp [mul_comm]
    rw [this, Complex.conj_re]; ring
  rw [g64r_frob, hS, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hD]
  have := Complex.normSq_apply d
  nlinarith [sq_nonneg (d.re - 1), sq_nonneg d.im]

lemma frobNorm_sq_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h_norm : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := Matrix.frobenius_norm_def A
  change ‖A‖ ^ 2 = _
  rw [h_norm]
  have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  have h_pow : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
  rw [h_pow]
  simp_rw [Real.rpow_two]

lemma trace_re_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ((Aᴴ * A).trace).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  have h_inner : ∀ j, (∑ i, star (A i j) * A i j).re = ∑ i, ‖A i j‖ ^ 2 := by
    intro j
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (A i j) * A i j = ((‖A i j‖ : ℂ) ^ 2) := RCLike.conj_mul (A i j)
    rw [this, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [h_inner]
  rw [Finset.sum_comm]

lemma frobNorm_sq_eq_trace_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((Aᴴ * A).trace).re := by
  rw [frobNorm_sq_eq, ← trace_re_eq]

lemma frobNorm_sq_eq_trace_mul_self_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((A * Aᴴ).trace).re := by
  rw [frobNorm_sq_eq_trace_re, Matrix.trace_mul_comm]

lemma frobNorm_left_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (X : Matrix m n ℂ) :
    frobNorm (V * X) = frobNorm X := by
  have hV_star : Vᴴ * V = (1 : Matrix m m ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hV
  have h_sq : frobNorm (V * X) ^ 2 = frobNorm X ^ 2 := by
    rw [frobNorm_sq_eq_trace_re, frobNorm_sq_eq_trace_re]
    have h_conj : (V * X)ᴴ = Xᴴ * Vᴴ := Matrix.conjTranspose_mul V X
    rw [h_conj]
    congr 2
    calc (Xᴴ * Vᴴ) * (V * X)
      _ = Xᴴ * (Vᴴ * (V * X)) := by rw [Matrix.mul_assoc]
      _ = Xᴴ * ((Vᴴ * V) * X) := by rw [← Matrix.mul_assoc Vᴴ V X]
      _ = Xᴴ * ((1 : Matrix m m ℂ) * X) := by rw [hV_star]
      _ = Xᴴ * X := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (V * X) := norm_nonneg _
  have h2 : 0 ≤ frobNorm X := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

lemma frobNorm_right_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (Y : Matrix m n ℂ) :
    frobNorm (Y * U) = frobNorm Y := by
  have hU_star : U * Uᴴ = (1 : Matrix n n ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have h_sq : frobNorm (Y * U) ^ 2 = frobNorm Y ^ 2 := by
    rw [frobNorm_sq_eq_trace_mul_self_re, frobNorm_sq_eq_trace_mul_self_re]
    have h_conj : (Y * U)ᴴ = Uᴴ * Yᴴ := Matrix.conjTranspose_mul Y U
    rw [h_conj]
    congr 2
    calc (Y * U) * (Uᴴ * Yᴴ)
      _ = Y * (U * (Uᴴ * Yᴴ)) := by rw [Matrix.mul_assoc]
      _ = Y * ((U * Uᴴ) * Yᴴ) := by rw [← Matrix.mul_assoc U Uᴴ Yᴴ]
      _ = Y * ((1 : Matrix n n ℂ) * Yᴴ) := by rw [hU_star]
      _ = Y * Yᴴ := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (Y * U) := norm_nonneg _
  have h2 : 0 ≤ frobNorm Y := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

def projMat {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * star (v j)

def ip {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) : ℂ :=
  ∑ k, star (a k) * b k

lemma refl_eq_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    householderReflection v = 1 - 2 • projMat v := by
  ext i j
  simp [householderReflection, projMat, Matrix.one_apply, mul_assoc]

set_option linter.unnecessarySeqFocus false in
lemma projMat_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    projMat v * projMat v = projMat v := by
  have hip : ip v v = 1 := by
    have nv : ∑ k, Complex.normSq (v k) = 1 := by rw [← g64r_nsq, hv]; norm_num
    have h1 : ip v v = ((∑ k, Complex.normSq (v k) : ℝ) : ℂ) := by
      rw [ip, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
    rw [h1, nv, Complex.ofReal_one]
  ext i j
  simp only [projMat, Matrix.mul_apply, Matrix.of_apply]
  have : ∑ k, v i * star (v k) * (v k * star (v j)) = v i * star (v j) * ip v v := by
    rw [ip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, hip, mul_one]

lemma projMat_star {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    star (projMat v) = projMat v := by
  ext i j
  simp [projMat, Matrix.star_apply, mul_comm]

lemma householder_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    householderReflection v ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [refl_eq_proj]
  set Q := projMat v
  have hQ : Q * Q = Q := projMat_mul_self v hv
  have hs : star Q = Q := projMat_star v
  rw [star_sub, star_one, star_nsmul, hs]
  have : (1 - 2 • Q) * (1 - 2 • Q) = 1 - 4 • Q + 4 • (Q * Q) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm]
    rw [show (2 : ℕ) * 2 = 4 by rfl]
    rw [show (4 : ℕ) • Q = 2 • Q + 2 • Q by rw [← add_smul]]
    abel
  rw [this, hQ]; abel

lemma frobNorm_mul_sub_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℂ)
    (hB : B ∈ Matrix.unitaryGroup ι ℂ)
    (hC : C ∈ Matrix.unitaryGroup ι ℂ) :
    frobNorm (A * B - C * D) ≤ frobNorm (A - C) + frobNorm (B - D) := by
  have h_id : (A - C) * B + C * (B - D) = A * B - C * D := by
    rw [sub_mul, mul_sub, sub_add_sub_cancel]
  rw [← h_id]
  have h_tri : frobNorm ((A - C) * B + C * (B - D)) ≤ frobNorm ((A - C) * B) + frobNorm (C * (B - D)) :=
    norm_add_le _ _
  rw [frobNorm_right_unitary_eq B hB (A - C), frobNorm_left_unitary_eq C hC (B - D)] at h_tri
  exact h_tri

/-! ### Part 2: Tensor vector identities and exact reflection factorization -/

lemma P_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : EuclideanSpace ℂ ι) (h : ip a b = 0) :
    projMat a * projMat b = 0 := by
  ext i j
  simp only [projMat, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have : ∑ k, a i * star (a k) * (b k * star (b j)) = a i * star (b j) * ip a b := by
    rw [ip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, h, mul_zero]

lemma tensor_false_apply {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (b : Bool) (z : Qubits n) :
    tensorVec (ket false) psi (b, z) = if b = false then psi z else 0 := by
  cases b <;> simp [tensorVec, ket]

lemma tensor_true_apply {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (b : Bool) (z : Qubits n) :
    tensorVec (ket true) psi (b, z) = if b = true then psi z else 0 := by
  cases b <;> simp [tensorVec, ket]

lemma isState_tensor_false {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi) :
    IsState (tensorVec (ket false) psi) := by
  unfold IsState at hpsi ⊢
  have hsq : ‖tensorVec (ket false) psi‖ ^ 2 = 1 := by
    rw [g64r_nsq, Fintype.sum_prod_type]
    have : (∑ b : Bool, ∑ x : Qubits n, Complex.normSq (tensorVec (ket false) psi (b, x))) =
        ∑ x : Qubits n, Complex.normSq (psi x) := by
      rw [Fintype.sum_bool]
      simp [tensor_false_apply]
    rw [this, ← g64r_nsq, hpsi, one_pow]
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)] at hsq

lemma isState_tensor_true {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi) :
    IsState (tensorVec (ket true) psi) := by
  unfold IsState at hpsi ⊢
  have hsq : ‖tensorVec (ket true) psi‖ ^ 2 = 1 := by
    rw [g64r_nsq, Fintype.sum_prod_type]
    have : (∑ b : Bool, ∑ x : Qubits n, Complex.normSq (tensorVec (ket true) psi (b, x))) =
        ∑ x : Qubits n, Complex.normSq (psi x) := by
      rw [Fintype.sum_bool]
      simp [tensor_true_apply]
    rw [this, ← g64r_nsq, hpsi, one_pow]
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)] at hsq

lemma ip_tensor_false_true {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) :
    ip (tensorVec (ket false) psi) (tensorVec (ket true) psi) = 0 := by
  rw [ip, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [tensor_false_apply, tensor_true_apply]

lemma householder_prod_tensor_eq {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) :
    householderReflection (tensorVec (ket false) psi) * householderReflection (tensorVec (ket true) psi) =
    identityExtension (householderReflection psi) := by
  set v0 := tensorVec (ket false) psi
  set v1 := tensorVec (ket true) psi
  have h01 : ip v0 v1 = 0 := ip_tensor_false_true psi
  rw [refl_eq_proj v0, refl_eq_proj v1]
  have hmul : (1 - 2 • projMat v0) * (1 - 2 • projMat v1) =
      1 - 2 • projMat v0 - 2 • projMat v1 := by
    calc (1 - 2 • projMat v0) * (1 - 2 • projMat v1)
      _ = 1 - 2 • projMat v0 - 2 • projMat v1 + 4 • (projMat v0 * projMat v1) := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm]
        norm_num; abel
      _ = 1 - 2 • projMat v0 - 2 • projMat v1 := by
        rw [P_mul v0 v1 h01, smul_zero, add_zero]
  rw [hmul]
  ext ⟨c, x⟩ ⟨d, y⟩
  simp only [identityExtension, householderReflection, projMat, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, Prod.mk.injEq]
  cases c <;> cases d <;> simp [v0, v1, tensor_false_apply, tensor_true_apply] <;> ring

lemma qubits_two_distinct {n : ℕ} (hn : 1 ≤ n) :
    ∃ z0 z1 : Qubits n, z0 ≠ z1 := by
  set z0 : Qubits n := fun _ => false
  set z1 : Qubits n := fun _ => true
  refine ⟨z0, z1, ?_⟩
  intro h
  have hz := congr_fun h ⟨0, hn⟩
  revert hz; decide

lemma tensor_false_two_zeros {n : ℕ} (hn : 1 ≤ n) (psi : EuclideanSpace ℂ (Qubits n)) :
    ∃ j l : Bool × Qubits n, j ≠ l ∧ tensorVec (ket false) psi j = 0 ∧ tensorVec (ket false) psi l = 0 := by
  obtain ⟨z0, z1, hz⟩ := qubits_two_distinct hn
  refine ⟨(true, z0), (true, z1), ?_, ?_, ?_⟩
  · intro h; injection h with _ h2; exact hz h2
  · exact tensor_false_apply psi true z0
  · exact tensor_false_apply psi true z1

lemma tensor_true_two_zeros {n : ℕ} (hn : 1 ≤ n) (psi : EuclideanSpace ℂ (Qubits n)) :
    ∃ j l : Bool × Qubits n, j ≠ l ∧ tensorVec (ket true) psi j = 0 ∧ tensorVec (ket true) psi l = 0 := by
  obtain ⟨z0, z1, hz⟩ := qubits_two_distinct hn
  refine ⟨(false, z0), (false, z1), ?_, ?_, ?_⟩
  · intro h; injection h with _ h2; exact hz h2
  · exact tensor_true_apply psi false z0
  · exact tensor_true_apply psi false z1

/-! ### Part 3: Truncation, four-squares deficit completion, and two-zero approximation -/

lemma floor_sq_le {x : ℝ} (hx : 0 ≤ x) : (⌊x⌋ : ℝ) ^ 2 ≤ x ^ 2 := by
  have h1 : 0 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hx
  have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  nlinarith

lemma floor_sub_sq_le {x : ℝ} : (x - (⌊x⌋ : ℝ)) ^ 2 ≤ 1 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x - 1 < (⌊x⌋ : ℝ) := Int.sub_one_lt_floor x
  nlinarith

lemma floor_sq_sub_sq_le {x : ℝ} (hx : 0 ≤ x) : x ^ 2 - (⌊x⌋ : ℝ) ^ 2 ≤ 2 * x := by
  have h1 : 0 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hx
  have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h3 : x - 1 < (⌊x⌋ : ℝ) := Int.sub_one_lt_floor x
  nlinarith

def truncInt (m : ℕ) (r : ℝ) : ℤ :=
  if 0 ≤ r then ⌊(2 : ℝ) ^ m * r⌋ else -⌊(2 : ℝ) ^ m * (-r)⌋

lemma two_pow_pos_real (m : ℕ) : (0 : ℝ) < (2 : ℝ) ^ m := by positivity

lemma truncInt_sq_le (m : ℕ) (r : ℝ) :
    ((truncInt m r : ℝ) / (2 : ℝ) ^ m) ^ 2 ≤ r ^ 2 := by
  have hp : 0 < (2 : ℝ) ^ m := two_pow_pos_real m
  unfold truncInt
  split_ifs with hr
  · have hx : 0 ≤ (2 : ℝ) ^ m * r := mul_nonneg (le_of_lt hp) hr
    have h := floor_sq_le hx
    have : ((⌊(2 : ℝ) ^ m * r⌋ : ℝ) / (2 : ℝ) ^ m) ^ 2 = (⌊(2 : ℝ) ^ m * r⌋ : ℝ) ^ 2 / ((2 : ℝ) ^ m) ^ 2 := by ring
    rw [this]
    have : r ^ 2 = ((2 : ℝ) ^ m * r) ^ 2 / ((2 : ℝ) ^ m) ^ 2 := by
      rw [mul_pow]; exact (mul_div_cancel_left₀ (r ^ 2) (by positivity)).symm
    rw [this]
    exact div_le_div_of_nonneg_right h (by positivity)
  · push Not at hr
    set u := -r with hu
    have hu0 : 0 ≤ u := by linarith
    have hx : 0 ≤ (2 : ℝ) ^ m * u := mul_nonneg (le_of_lt hp) hu0
    have h := floor_sq_le hx
    have hcast : ((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) = -((⌊(2 : ℝ) ^ m * u⌋ : ℤ) : ℝ) := by
      rw [← hu, Int.cast_neg]
    have : (((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) / (2 : ℝ) ^ m) ^ 2 =
        (⌊(2 : ℝ) ^ m * u⌋ : ℝ) ^ 2 / ((2 : ℝ) ^ m) ^ 2 := by
      rw [hcast]; ring
    rw [this]
    have : r ^ 2 = ((2 : ℝ) ^ m * u) ^ 2 / ((2 : ℝ) ^ m) ^ 2 := by
      have : r ^ 2 = u ^ 2 := by rw [hu]; ring
      rw [this, mul_pow]
      exact (mul_div_cancel_left₀ (u ^ 2) (by positivity)).symm
    rw [this]
    exact div_le_div_of_nonneg_right h (by positivity)

lemma truncInt_sub_sq_le (m : ℕ) (r : ℝ) :
    (r - (truncInt m r : ℝ) / (2 : ℝ) ^ m) ^ 2 ≤ ((2 : ℝ) ^ m)⁻¹ ^ 2 := by
  have hp : 0 < (2 : ℝ) ^ m := two_pow_pos_real m
  have hne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hp
  unfold truncInt
  split_ifs with hr
  · have h := @floor_sub_sq_le ((2 : ℝ) ^ m * r)
    have : r - (⌊(2 : ℝ) ^ m * r⌋ : ℝ) / (2 : ℝ) ^ m = ((2 : ℝ) ^ m * r - (⌊(2 : ℝ) ^ m * r⌋ : ℝ)) / (2 : ℝ) ^ m := by
      field_simp
    rw [this, div_pow]
    have hinv : ((2 : ℝ) ^ m)⁻¹ ^ 2 = 1 / ((2 : ℝ) ^ m) ^ 2 := by ring
    rw [hinv]
    exact div_le_div_of_nonneg_right h (by positivity)
  · push Not at hr
    set u := -r with hu
    have h := @floor_sub_sq_le ((2 : ℝ) ^ m * u)
    have hcast : ((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) = -((⌊(2 : ℝ) ^ m * u⌋ : ℤ) : ℝ) := by
      rw [← hu, Int.cast_neg]
    have hsq : (r - ((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) / (2 : ℝ) ^ m) ^ 2 =
        (((2 : ℝ) ^ m * u - (⌊(2 : ℝ) ^ m * u⌋ : ℝ)) / (2 : ℝ) ^ m) ^ 2 := by
      have : r - ((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) / (2 : ℝ) ^ m =
          -(((2 : ℝ) ^ m * u - (⌊(2 : ℝ) ^ m * u⌋ : ℝ)) / (2 : ℝ) ^ m) := by
        rw [hcast, hu]; field_simp; ring
      rw [this]; ring
    rw [hsq, div_pow]
    have hinv : ((2 : ℝ) ^ m)⁻¹ ^ 2 = 1 / ((2 : ℝ) ^ m) ^ 2 := by ring
    rw [hinv]
    exact div_le_div_of_nonneg_right h (by positivity)

lemma truncInt_sq_sub_sq_le (m : ℕ) (r : ℝ) :
    r ^ 2 - ((truncInt m r : ℝ) / (2 : ℝ) ^ m) ^ 2 ≤ 2 * |r| / (2 : ℝ) ^ m := by
  have hp : 0 < (2 : ℝ) ^ m := two_pow_pos_real m
  have hne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hp
  unfold truncInt
  split_ifs with hr
  · have hx : 0 ≤ (2 : ℝ) ^ m * r := mul_nonneg (le_of_lt hp) hr
    have h := floor_sq_sub_sq_le hx
    have : r ^ 2 - ((⌊(2 : ℝ) ^ m * r⌋ : ℝ) / (2 : ℝ) ^ m) ^ 2 =
        (((2 : ℝ) ^ m * r) ^ 2 - (⌊(2 : ℝ) ^ m * r⌋ : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
      field_simp
    rw [this]
    have hle : (((2 : ℝ) ^ m * r) ^ 2 - (⌊(2 : ℝ) ^ m * r⌋ : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 ≤
        (2 * ((2 : ℝ) ^ m * r)) / ((2 : ℝ) ^ m) ^ 2 :=
      div_le_div_of_nonneg_right h (by positivity)
    have heq : (2 * ((2 : ℝ) ^ m * r)) / ((2 : ℝ) ^ m) ^ 2 = 2 * |r| / (2 : ℝ) ^ m := by
      rw [abs_of_nonneg hr]
      calc (2 * ((2 : ℝ) ^ m * r)) / ((2 : ℝ) ^ m) ^ 2
        _ = ((2 * r) * (2 : ℝ) ^ m) / (((2 : ℝ) ^ m) * (2 : ℝ) ^ m) := by ring
        _ = (2 * r) / (2 : ℝ) ^ m := mul_div_mul_right (2 * r) _ (ne_of_gt hp)
    exact hle.trans_eq heq
  · push Not at hr
    set u := -r with hu
    have hu0 : 0 ≤ u := by linarith
    have hx : 0 ≤ (2 : ℝ) ^ m * u := mul_nonneg (le_of_lt hp) hu0
    have h := floor_sq_sub_sq_le hx
    have hcast : ((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) = -((⌊(2 : ℝ) ^ m * u⌋ : ℤ) : ℝ) := by
      rw [← hu, Int.cast_neg]
    have : r ^ 2 - (((-⌊(2 : ℝ) ^ m * (-r)⌋ : ℤ) : ℝ) / (2 : ℝ) ^ m) ^ 2 =
        (((2 : ℝ) ^ m * u) ^ 2 - (⌊(2 : ℝ) ^ m * u⌋ : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
      have hr_eq : r = -u := by linarith
      rw [hcast, hr_eq]
      field_simp
    rw [this]
    have hle : (((2 : ℝ) ^ m * u) ^ 2 - (⌊(2 : ℝ) ^ m * u⌋ : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 ≤
        (2 * ((2 : ℝ) ^ m * u)) / ((2 : ℝ) ^ m) ^ 2 :=
      div_le_div_of_nonneg_right h (by positivity)
    have heq : (2 * ((2 : ℝ) ^ m * u)) / ((2 : ℝ) ^ m) ^ 2 = 2 * |r| / (2 : ℝ) ^ m := by
      have : |r| = u := by rw [hu]; exact abs_of_neg hr
      rw [this]
      calc (2 * ((2 : ℝ) ^ m * u)) / ((2 : ℝ) ^ m) ^ 2
        _ = ((2 * u) * (2 : ℝ) ^ m) / (((2 : ℝ) ^ m) * (2 : ℝ) ^ m) := by ring
        _ = (2 * u) / (2 : ℝ) ^ m := mul_div_mul_right (2 * u) _ (ne_of_gt hp)
    exact hle.trans_eq heq

lemma two_abs_le_sq {K u : ℝ} (hK : 0 < K) : 2 * |u| ≤ K * u ^ 2 + 1 / K := by
  have h : 0 ≤ (K * |u| - 1) ^ 2 := sq_nonneg _
  have heq : (K * |u| - 1) ^ 2 = K ^ 2 * u ^ 2 - 2 * K * |u| + 1 := by
    have : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith
  rw [heq] at h
  have : 2 * K * |u| ≤ K ^ 2 * u ^ 2 + 1 := by linarith
  have hdiv : 2 * K * |u| / K ≤ (K ^ 2 * u ^ 2 + 1) / K := by
    rwa [div_le_div_iff_of_pos_right hK]
  have hleft : 2 * K * |u| / K = 2 * |u| := by
    calc 2 * K * |u| / K = (2 * |u|) * K / K := by ring
    _ = 2 * |u| := mul_div_cancel_right₀ _ (ne_of_gt hK)
  have hright : (K ^ 2 * u ^ 2 + 1) / K = K * u ^ 2 + 1 / K := by
    calc (K ^ 2 * u ^ 2 + 1) / K = (K * u ^ 2) * K / K + 1 / K := by ring
    _ = K * u ^ 2 + 1 / K := by rw [mul_div_cancel_right₀ _ (ne_of_gt hK)]
  rwa [hleft, hright] at hdiv

lemma sum_univ_erase_two {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (j l : ι) (hjl : j ≠ l) (f : ι → M) :
    ∑ x, f x = f j + f l + ∑ x ∈ (Finset.univ.erase j).erase l, f x := by
  set S := (Finset.univ.erase j).erase l
  have hj : j ∉ Finset.univ.erase j := by simp
  have hl_in : l ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hjl.symm, Finset.mem_univ l⟩
  have hl : l ∉ S := by simp [S]
  have heq : insert l S = Finset.univ.erase j := Finset.insert_erase hl_in
  have huniv : (Finset.univ : Finset ι) = insert j (insert l S) := by
    rw [heq, Finset.insert_erase (Finset.mem_univ j)]
  conv_lhs => rw [huniv]
  have hj_not : j ∉ insert l S := by rw [heq]; exact hj
  rw [Finset.sum_insert hj_not, Finset.sum_insert hl, add_assoc]

lemma four_pow_eq_two_pow_sq (m : ℕ) : (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := by
  have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [this, ← pow_mul, mul_comm, pow_mul]

lemma normSq_div_two_pow (z : ℂ) (m : ℕ) :
    Complex.normSq (z / (2 : ℂ) ^ m) = Complex.normSq z / ((2 : ℝ) ^ m) ^ 2 := by
  rw [map_div₀, map_pow Complex.normSq]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2, four_pow_eq_two_pow_sq]

lemma normSq_nat_add_I_nat (a b : ℕ) :
    Complex.normSq ((a : ℂ) + Complex.I * (b : ℂ)) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma normSq_int_add_I_int (a b : ℤ) :
    Complex.normSq ((a : ℂ) + Complex.I * (b : ℂ)) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma normSq_nat_div_two_pow (a b : ℕ) (m : ℕ) :
    Complex.normSq (((a : ℂ) + Complex.I * (b : ℂ)) / (2 : ℂ) ^ m) =
    ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
  rw [normSq_div_two_pow, normSq_nat_add_I_nat]

lemma normSq_int_div_two_pow (a b : ℤ) (m : ℕ) :
    Complex.normSq (((a : ℂ) + Complex.I * (b : ℂ)) / (2 : ℂ) ^ m) =
    ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
  rw [normSq_div_two_pow, normSq_int_add_I_int]

lemma normSq_real_add_I_real (u v : ℝ) :
    Complex.normSq ((u : ℂ) + Complex.I * (v : ℂ)) = u ^ 2 + v ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma div_two_pow_complex (a b : ℤ) (m : ℕ) :
    ((a : ℂ) + Complex.I * (b : ℂ)) / (2 : ℂ) ^ m =
    (((a : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ) + Complex.I * (((b : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ) := by
  have h2 : (2 : ℂ) ^ m = (((2 : ℝ) ^ m : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, add_div, mul_div_assoc]
  congr 1
  · push_cast; rfl
  · congr 1
    push_cast; rfl

lemma two_zero_approx {ι : Type*} [Fintype ι] [DecidableEq ι]
    (psi : EuclideanSpace ℂ ι) (hpsi : IsState psi)
    (j l : ι) (hjl : j ≠ l) (hj : psi j = 0) (hl : psi l = 0)
    (m : ℕ) (K : ℝ) (hK : 0 < K) (hmK : K ≤ (2 : ℝ) ^ m) :
    ∃ phi : EuclideanSpace ℂ ι,
      IsState phi ∧
      (∀ z, HasDenominator 2 m (phi z)) ∧
      ‖phi - psi‖ ^ 2 ≤ ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card ι : ℝ) / K) := by
  set S := (Finset.univ.erase j).erase l
  have hjS : j ∉ S := by simp [S]
  have hlS : l ∉ S := by simp [S]
  have hp : 0 < (2 : ℝ) ^ m := two_pow_pos_real m
  have hp2 : 0 < ((2 : ℝ) ^ m) ^ 2 := by positivity

  have hpsi1 : ∑ x, Complex.normSq (psi x) = 1 := by rw [← g64r_nsq, hpsi]; norm_num
  have hpsi_S : ∑ x ∈ S, Complex.normSq (psi x) = 1 := by
    have := sum_univ_erase_two j l hjl (fun x => Complex.normSq (psi x))
    rw [hj, hl] at this
    simp only [map_zero, zero_add] at this
    rw [hpsi1] at this
    exact this.symm

  have h_trunc_le : ∑ z ∈ S, (((truncInt m (psi z).re : ℝ) / (2 : ℝ) ^ m) ^ 2 +
      ((truncInt m (psi z).im : ℝ) / (2 : ℝ) ^ m) ^ 2) ≤ 1 := by
    have : ∑ z ∈ S, (((truncInt m (psi z).re : ℝ) / (2 : ℝ) ^ m) ^ 2 +
        ((truncInt m (psi z).im : ℝ) / (2 : ℝ) ^ m) ^ 2) ≤
        ∑ z ∈ S, (((psi z).re) ^ 2 + ((psi z).im) ^ 2) := by
      refine Finset.sum_le_sum fun z hz => ?_
      exact add_le_add (truncInt_sq_le m _) (truncInt_sq_le m _)
    have hnorm : ∀ z, ((psi z).re) ^ 2 + ((psi z).im) ^ 2 = Complex.normSq (psi z) := by
      intro z; simp [Complex.normSq_apply]; ring
    simp_rw [hnorm, hpsi_S] at this
    exact this

  have h_trunc_sum_le : ∑ z ∈ S, ((truncInt m (psi z).re : ℝ) ^ 2 + (truncInt m (psi z).im : ℝ) ^ 2) ≤ ((2 : ℝ) ^ m) ^ 2 := by
    have hsum_eq : ∑ z ∈ S, (((truncInt m (psi z).re : ℝ) / (2 : ℝ) ^ m) ^ 2 + ((truncInt m (psi z).im : ℝ) / (2 : ℝ) ^ m) ^ 2) =
        (∑ z ∈ S, ((truncInt m (psi z).re : ℝ) ^ 2 + (truncInt m (psi z).im : ℝ) ^ 2)) / ((2 : ℝ) ^ m) ^ 2 := by
      have : ∀ z ∈ S, (((truncInt m (psi z).re : ℝ) / (2 : ℝ) ^ m) ^ 2 + ((truncInt m (psi z).im : ℝ) / (2 : ℝ) ^ m) ^ 2) =
          ((truncInt m (psi z).re : ℝ) ^ 2 + (truncInt m (psi z).im : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
        intro z hz; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_div]
    rw [hsum_eq] at h_trunc_le
    have hmul := (div_le_iff₀ hp2).mp h_trunc_le
    rwa [one_mul] at hmul

  have h4 : ((2 : ℝ) ^ m) ^ 2 = ((4 : ℤ) ^ m : ℝ) := by
    have : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, ← pow_mul, mul_comm, pow_mul]
    rw [this]
    push_cast; rfl
  have h_int_le : ∑ z ∈ S, (truncInt m (psi z).re ^ 2 + truncInt m (psi z).im ^ 2) ≤ (4 ^ m : ℤ) := by
    exact_mod_cast (h_trunc_sum_le.trans_eq h4)

  set D : ℤ := (4 ^ m : ℤ) - ∑ z ∈ S, (truncInt m (psi z).re ^ 2 + truncInt m (psi z).im ^ 2)
  have hD0 : 0 ≤ D := sub_nonneg.mpr h_int_le
  obtain ⟨n1, n2, n3, n4, hn⟩ := Nat.sum_four_squares D.toNat
  have hD_eq : (n1 : ℤ) ^ 2 + (n2 : ℤ) ^ 2 + (n3 : ℤ) ^ 2 + (n4 : ℤ) ^ 2 = D := by
    have : (n1 : ℤ) ^ 2 + (n2 : ℤ) ^ 2 + (n3 : ℤ) ^ 2 + (n4 : ℤ) ^ 2 = (D.toNat : ℤ) := by
      exact_mod_cast hn
    rw [this, Int.toNat_of_nonneg hD0]

  set phi_fn : ι → ℂ := fun z =>
    if z = j then ((n1 : ℂ) + Complex.I * (n2 : ℂ)) / (2 : ℂ) ^ m
    else if z = l then ((n3 : ℂ) + Complex.I * (n4 : ℂ)) / (2 : ℂ) ^ m
    else ((truncInt m (psi z).re : ℂ) + Complex.I * (truncInt m (psi z).im : ℂ)) / (2 : ℂ) ^ m
  set phi : EuclideanSpace ℂ ι := WithLp.toLp 2 phi_fn

  have hphi_j : phi j = ((n1 : ℂ) + Complex.I * (n2 : ℂ)) / (2 : ℂ) ^ m := by
    simp [phi, phi_fn]
  have hphi_l : phi l = ((n3 : ℂ) + Complex.I * (n4 : ℂ)) / (2 : ℂ) ^ m := by
    simp [phi, phi_fn, hjl.symm]
  have hphi_S : ∀ z ∈ S, phi z = ((truncInt m (psi z).re : ℂ) + Complex.I * (truncInt m (psi z).im : ℂ)) / (2 : ℂ) ^ m := by
    intro z hz
    have hzj : z ≠ j := by intro h; subst h; exact hjS hz
    have hzl : z ≠ l := by intro h; subst h; exact hlS hz
    simp [phi, phi_fn, hzj, hzl]

  have h_denom : ∀ z, HasDenominator 2 m (phi z) := by
    intro z
    by_cases hzj : z = j
    · subst hzj; rw [hphi_j]; refine ⟨n1, 0, n2, 0, ?_⟩; simp
    · by_cases hzl : z = l
      · subst hzl; rw [hphi_l]; refine ⟨n3, 0, n4, 0, ?_⟩; simp
      · have : phi z = ((truncInt m (psi z).re : ℂ) + Complex.I * (truncInt m (psi z).im : ℂ)) / (2 : ℂ) ^ m := by
          simp [phi, phi_fn, hzj, hzl]
        rw [this]; refine ⟨truncInt m (psi z).re, 0, truncInt m (psi z).im, 0, ?_⟩; simp

  have h_state : IsState phi := by
    unfold IsState
    have hsq : ‖phi‖ ^ 2 = 1 := by
      rw [g64r_nsq]
      have hsum := sum_univ_erase_two j l hjl (fun x => Complex.normSq (phi x))
      change ∑ x, Complex.normSq (phi x) = Complex.normSq (phi j) + Complex.normSq (phi l) + ∑ x ∈ S, Complex.normSq (phi x) at hsum
      rw [hphi_j, hphi_l] at hsum
      rw [normSq_nat_div_two_pow, normSq_nat_div_two_pow] at hsum
      have hS_sum : ∑ x ∈ S, Complex.normSq (phi x) =
          (∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2)) / ((2 : ℝ) ^ m) ^ 2 := by
        have : ∀ x ∈ S, Complex.normSq (phi x) =
            ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by
          intro x hx
          rw [hphi_S x hx, normSq_int_div_two_pow]
        rw [Finset.sum_congr rfl this, ← Finset.sum_div]
      rw [hS_sum] at hsum
      rw [hsum]
      have hD_real : (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2 = (D : ℝ) := by
        exact_mod_cast hD_eq
      have hcomb : ((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 +
          ((n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 +
          (∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2)) / ((2 : ℝ) ^ m) ^ 2 =
          (((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2) +
            ∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2)) / ((2 : ℝ) ^ m) ^ 2 := by
        ring
      rw [hcomb, hD_real]
      have hD_def : (D : ℝ) + ∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2) =
          ((2 : ℝ) ^ m) ^ 2 := by
        have : (D : ℝ) = ((4 : ℤ) ^ m : ℝ) - ∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2) := by
          dsimp [D]; push_cast; ring
        rw [this, sub_add_cancel, ← h4]
      rw [hD_def, div_self (ne_of_gt hp2)]
    rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)] at hsq

  have h_dist : ‖phi - psi‖ ^ 2 ≤ ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card ι : ℝ) / K) := by
    rw [g64r_nsq]
    have hsum := sum_univ_erase_two j l hjl (fun x => Complex.normSq (phi x - psi x))
    change ∑ x, Complex.normSq (phi x - psi x) = Complex.normSq (phi j - psi j) + Complex.normSq (phi l - psi l) + ∑ x ∈ S, Complex.normSq (phi x - psi x) at hsum
    rw [hj, hl] at hsum
    have e1 : phi j - 0 = phi j := sub_zero _
    have e2 : phi l - 0 = phi l := sub_zero _
    rw [e1, e2, hphi_j, hphi_l] at hsum
    rw [normSq_nat_div_two_pow, normSq_nat_div_two_pow] at hsum
    have hD_real : (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2 = (D : ℝ) := by
      exact_mod_cast hD_eq
    have h12 : ((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 +
        ((n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 = (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 := by
      calc ((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 + ((n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2
        _ = ((n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2) / ((2 : ℝ) ^ m) ^ 2 := by ring
        _ = (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 := by rw [hD_real]
    rw [h12] at hsum
    change ∑ i, Complex.normSq (phi i - psi i) ≤ _
    rw [hsum]

    have hS_le : ∑ x ∈ S, Complex.normSq (phi x - psi x) ≤ 2 * (Fintype.card ι : ℝ) / ((2 : ℝ) ^ m) ^ 2 := by
      have : ∀ x ∈ S, Complex.normSq (phi x - psi x) ≤ 2 * ((2 : ℝ) ^ m)⁻¹ ^ 2 := by
        intro x hx
        rw [hphi_S x hx]
        have hdiv := div_two_pow_complex (truncInt m (psi x).re) (truncInt m (psi x).im) m
        have heq : ((truncInt m (psi x).re : ℂ) + Complex.I * (truncInt m (psi x).im : ℂ)) / (2 : ℂ) ^ m - psi x =
            (((truncInt m (psi x).re : ℝ) / (2 : ℝ) ^ m - (psi x).re : ℝ) : ℂ) +
            Complex.I * (((truncInt m (psi x).im : ℝ) / (2 : ℝ) ^ m - (psi x).im : ℝ) : ℂ) := by
          rw [hdiv]
          have hpsi_eq : psi x = ((psi x).re : ℂ) + Complex.I * ((psi x).im : ℂ) := by
            rw [mul_comm Complex.I ((psi x).im : ℂ)]
            exact (Complex.re_add_im (psi x)).symm
          conv_lhs =>
            enter [2]
            rw [hpsi_eq]
          push_cast
          ring
        rw [heq, normSq_real_add_I_real]
        have h1 := truncInt_sub_sq_le m (psi x).re
        have h2 := truncInt_sub_sq_le m (psi x).im
        have : ((truncInt m (psi x).re : ℝ) / (2 : ℝ) ^ m - (psi x).re) ^ 2 =
            ((psi x).re - (truncInt m (psi x).re : ℝ) / (2 : ℝ) ^ m) ^ 2 := by ring
        rw [this]
        have : ((truncInt m (psi x).im : ℝ) / (2 : ℝ) ^ m - (psi x).im) ^ 2 =
            ((psi x).im - (truncInt m (psi x).im : ℝ) / (2 : ℝ) ^ m) ^ 2 := by ring
        rw [this]
        linarith
      have hsum_le : ∑ x ∈ S, Complex.normSq (phi x - psi x) ≤ ∑ x ∈ S, (2 * ((2 : ℝ) ^ m)⁻¹ ^ 2) :=
        Finset.sum_le_sum this
      have hcard : (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast (Finset.card_le_card (Finset.subset_univ S))
      have : ∑ x ∈ S, (2 * ((2 : ℝ) ^ m)⁻¹ ^ 2) = (S.card : ℝ) * (2 * ((2 : ℝ) ^ m)⁻¹ ^ 2) := by simp
      rw [this] at hsum_le
      have hinv : ((2 : ℝ) ^ m)⁻¹ ^ 2 = 1 / ((2 : ℝ) ^ m) ^ 2 := by ring
      rw [hinv] at hsum_le
      have : (S.card : ℝ) * (2 * (1 / ((2 : ℝ) ^ m) ^ 2)) ≤ (Fintype.card ι : ℝ) * (2 * (1 / ((2 : ℝ) ^ m) ^ 2)) := by
        nlinarith
      have heq2 : (Fintype.card ι : ℝ) * (2 * (1 / ((2 : ℝ) ^ m) ^ 2)) = 2 * (Fintype.card ι : ℝ) / ((2 : ℝ) ^ m) ^ 2 := by ring
      linarith

    have hD_bound : (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 ≤ ((2 : ℝ) ^ m)⁻¹ * (K + 2 * (Fintype.card ι : ℝ) / K) := by
      have hD_split : (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 =
          ∑ x ∈ S, (((psi x).re ^ 2 - ((truncInt m (psi x).re : ℝ) / (2 : ℝ) ^ m) ^ 2) +
                   ((psi x).im ^ 2 - ((truncInt m (psi x).im : ℝ) / (2 : ℝ) ^ m) ^ 2)) := by
        have : (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 = 1 - (∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2)) / ((2 : ℝ) ^ m) ^ 2 := by
          have hD_def : (D : ℝ) = ((4 : ℤ) ^ m : ℝ) - ∑ x ∈ S, ((truncInt m (psi x).re : ℝ) ^ 2 + (truncInt m (psi x).im : ℝ) ^ 2) := by
            dsimp [D]; push_cast; ring
          rw [hD_def, sub_div]
          have : ((4 : ℤ) ^ m : ℝ) / ((2 : ℝ) ^ m) ^ 2 = 1 := by rw [← h4, div_self (ne_of_gt hp2)]
          rw [this]
        rw [this]
        have h1_eq : (1 : ℝ) = ∑ x ∈ S, ((psi x).re ^ 2 + (psi x).im ^ 2) := by
          have hnorm : ∀ x, (psi x).re ^ 2 + (psi x).im ^ 2 = Complex.normSq (psi x) := by
            intro x; simp [Complex.normSq_apply]; ring
          simp_rw [hnorm, hpsi_S]
        rw [h1_eq, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        simp_rw [div_pow]
        ring
      rw [hD_split]
      have hterm_le : ∀ x ∈ S, (((psi x).re ^ 2 - ((truncInt m (psi x).re : ℝ) / (2 : ℝ) ^ m) ^ 2) +
          ((psi x).im ^ 2 - ((truncInt m (psi x).im : ℝ) / (2 : ℝ) ^ m) ^ 2)) ≤
          ((2 : ℝ) ^ m)⁻¹ * (2 * |(psi x).re| + 2 * |(psi x).im|) := by
        intro x hx
        have h1 := truncInt_sq_sub_sq_le m (psi x).re
        have h2 := truncInt_sq_sub_sq_le m (psi x).im
        have : 2 * |(psi x).re| / (2 : ℝ) ^ m + 2 * |(psi x).im| / (2 : ℝ) ^ m =
            ((2 : ℝ) ^ m)⁻¹ * (2 * |(psi x).re| + 2 * |(psi x).im|) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        linarith
      have hsum_le := Finset.sum_le_sum hterm_le
      have : (∑ x ∈ S, ((2 : ℝ) ^ m)⁻¹ * (2 * |(psi x).re| + 2 * |(psi x).im|)) =
          ((2 : ℝ) ^ m)⁻¹ * ∑ x ∈ S, (2 * |(psi x).re| + 2 * |(psi x).im|) := by
        rw [Finset.mul_sum]
      rw [this] at hsum_le
      have hamgm : ∑ x ∈ S, (2 * |(psi x).re| + 2 * |(psi x).im|) ≤ K + 2 * (Fintype.card ι : ℝ) / K := by
        have : ∀ x ∈ S, 2 * |(psi x).re| + 2 * |(psi x).im| ≤
            K * Complex.normSq (psi x) + 2 / K := by
          intro x hx
          have h1 := two_abs_le_sq hK (u := (psi x).re)
          have h2 := two_abs_le_sq hK (u := (psi x).im)
          have hnorm : Complex.normSq (psi x) = (psi x).re ^ 2 + (psi x).im ^ 2 := by
            simp [Complex.normSq_apply]; ring
          rw [hnorm]
          calc 2 * |(psi x).re| + 2 * |(psi x).im|
            _ ≤ (K * (psi x).re ^ 2 + 1 / K) + (K * (psi x).im ^ 2 + 1 / K) := add_le_add h1 h2
            _ = K * ((psi x).re ^ 2 + (psi x).im ^ 2) + 2 / K := by ring
        have hsum2 := Finset.sum_le_sum this
        have hK_sum : ∑ x ∈ S, (K * Complex.normSq (psi x) + 2 / K) =
            K * (∑ x ∈ S, Complex.normSq (psi x)) + (S.card : ℝ) * (2 / K) := by
          simp [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hK_sum, hpsi_S, mul_one] at hsum2
        have hcard : (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast (Finset.card_le_card (Finset.subset_univ S))
        have : (S.card : ℝ) * (2 / K) ≤ (Fintype.card ι : ℝ) * (2 / K) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
        have : (Fintype.card ι : ℝ) * (2 / K) = 2 * (Fintype.card ι : ℝ) / K := by ring
        linarith
      have hpos_inv : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
      have : ((2 : ℝ) ^ m)⁻¹ * (∑ x ∈ S, (2 * |(psi x).re| + 2 * |(psi x).im|)) ≤
          ((2 : ℝ) ^ m)⁻¹ * (K + 2 * (Fintype.card ι : ℝ) / K) :=
        mul_le_mul_of_nonneg_left hamgm hpos_inv
      linarith

    have hS_bound2 : 2 * (Fintype.card ι : ℝ) / ((2 : ℝ) ^ m) ^ 2 ≤
        ((2 : ℝ) ^ m)⁻¹ * (2 * (Fintype.card ι : ℝ) / K) := by
      have : ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ m * (2 : ℝ) ^ m := sq _
      rw [this]
      have : 2 * (Fintype.card ι : ℝ) / ((2 : ℝ) ^ m * (2 : ℝ) ^ m) =
          ((2 : ℝ) ^ m)⁻¹ * (2 * (Fintype.card ι : ℝ) / (2 : ℝ) ^ m) := by
        field_simp
      rw [this]
      have hdiv : 2 * (Fintype.card ι : ℝ) / (2 : ℝ) ^ m ≤ 2 * (Fintype.card ι : ℝ) / K := by
        exact div_le_div_of_nonneg_left (by positivity) hK hmK
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)

    calc (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 + ∑ x ∈ S, Complex.normSq (phi x - psi x)
      _ ≤ (D : ℝ) / ((2 : ℝ) ^ m) ^ 2 + 2 * (Fintype.card ι : ℝ) / ((2 : ℝ) ^ m) ^ 2 := add_le_add le_rfl hS_le
      _ ≤ ((2 : ℝ) ^ m)⁻¹ * (K + 2 * (Fintype.card ι : ℝ) / K) + ((2 : ℝ) ^ m)⁻¹ * (2 * (Fintype.card ι : ℝ) / K) := add_le_add hD_bound hS_bound2
      _ = ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card ι : ℝ) / K) := by ring

  exact ⟨phi, h_state, h_denom, h_dist⟩

/-! ### Part 4: Analytical bounds on exponent and approximation error -/

lemma card_qubits_le_sq (n : ℕ) :
    (Fintype.card (Qubits n) : ℝ) ≤ ((2 : ℝ) ^ ((n + 1) / 2)) ^ 2 := by
  have : Fintype.card (Qubits n) = 2 ^ n := by
    simp [Qubits, Fintype.card_pi, Fintype.card_fin]
  rw [this]
  push_cast
  have hle : n ≤ ((n + 1) / 2) * 2 := by omega
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (((n + 1) / 2) * 2) :=
    pow_le_pow_right₀ (by norm_num) hle
  rw [pow_mul] at h2
  exact h2

lemma card_bool_qubits_le_two_mul_sq (n : ℕ) :
    (Fintype.card (Bool × Qubits n) : ℝ) ≤ 2 * ((2 : ℝ) ^ ((n + 1) / 2)) ^ 2 := by
  have : Fintype.card (Bool × Qubits n) = 2 * 2 ^ n := by
    simp [Qubits, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  rw [this]
  push_cast
  have hle : n ≤ ((n + 1) / 2) * 2 := by omega
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (((n + 1) / 2) * 2) :=
    pow_le_pow_right₀ (by norm_num) hle
  rw [pow_mul] at h2
  nlinarith [h2]

lemma two_pow_r_ge_inv_eps (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    let r := Nat.ceil (Real.log (1 / eps) / Real.log 2)
    1 / eps ≤ (2 : ℝ) ^ r := by
  intro r
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv_ge1 : 1 ≤ 1 / eps := by
    rw [le_div_iff₀ heps0]
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 / eps) := Real.log_nonneg hinv_ge1
  have hx_nonneg : 0 ≤ Real.log (1 / eps) / Real.log 2 := div_nonneg hlog_nonneg hlog2.le
  have h_le : Real.log (1 / eps) / Real.log 2 ≤ (r : ℝ) := Nat.le_ceil _
  have h_mul : Real.log (1 / eps) ≤ (r : ℝ) * Real.log 2 := by
    rwa [div_le_iff₀ hlog2] at h_le
  rw [← Real.log_pow 2 r] at h_mul
  have h2pos : 0 < (2 : ℝ) ^ r := by positivity
  have h_exp := (Real.log_le_log_iff (by positivity) h2pos).mp h_mul
  exact h_exp

lemma m_upper_bound (n : ℕ) (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    let r := Nat.ceil (Real.log (1 / eps) / Real.log 2)
    let m := (n + 1) / 2 + 2 * r + 9
    (m : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) + 11 * (1 + Real.log (1 / eps) / Real.log 2) := by
  intro r m
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv_ge1 : 1 ≤ 1 / eps := by
    rw [le_div_iff₀ heps0]
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 / eps) := Real.log_nonneg hinv_ge1
  have hx_nonneg : 0 ≤ Real.log (1 / eps) / Real.log 2 := div_nonneg hlog_nonneg hlog2.le
  have hr_le : (r : ℝ) ≤ Real.log (1 / eps) / Real.log 2 + 1 := (Nat.ceil_lt_add_one hx_nonneg).le
  dsimp [m]
  push_cast
  linarith

lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have hab := sq_le_sq.mp h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at hab

lemma sq_le_sq_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hb : 0 ≤ b := ha.trans h
  have hab : |a| ≤ |b| := by rwa [abs_of_nonneg ha, abs_of_nonneg hb]
  exact sq_le_sq.mpr hab

lemma single_error_bound_chain (u eps : ℝ) (r : ℕ)
    (hu : 0 ≤ u) (heps0 : 0 < eps)
    (hinv : 1 / eps ≤ (2 : ℝ) ^ r)
    (hu_sq : u ^ 2 ≤ 40 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) :
    u ≤ eps := by
  have h2pow : (2 : ℝ) ^ (2 * r + 9) = ((2 : ℝ) ^ r) ^ 2 * 512 := by
    rw [pow_add, ← pow_mul, mul_comm 2 r, pow_mul]
    norm_num
  have hinv_split : ((2 : ℝ) ^ (2 * r + 9))⁻¹ = (((2 : ℝ) ^ r) ^ 2)⁻¹ * (512 : ℝ)⁻¹ := by
    rw [h2pow, mul_inv]
  have h40 : 40 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ ≤ (((2 : ℝ) ^ r) ^ 2)⁻¹ := by
    rw [hinv_split]
    have : 40 * ((((2 : ℝ) ^ r) ^ 2)⁻¹ * (512 : ℝ)⁻¹) = (40 * (512 : ℝ)⁻¹) * (((2 : ℝ) ^ r) ^ 2)⁻¹ := by ring
    rw [this]
    have hfrac : 40 * (512 : ℝ)⁻¹ ≤ 1 := by norm_num
    have hpos : 0 ≤ (((2 : ℝ) ^ r) ^ 2)⁻¹ := by positivity
    exact mul_le_of_le_one_left hpos hfrac
  have h_inv_sq : (((2 : ℝ) ^ r) ^ 2)⁻¹ = (((2 : ℝ) ^ r)⁻¹) ^ 2 := by rw [inv_pow]
  have h1 : 1 ≤ (2 : ℝ) ^ r * eps := by rwa [div_le_iff₀ heps0] at hinv
  have h2pos : 0 < (2 : ℝ) ^ r := by positivity
  have h_eps_le : ((2 : ℝ) ^ r)⁻¹ ≤ eps := by
    rw [inv_eq_one_div]
    refine (div_le_iff₀ h2pos).mpr ?_
    linarith
  have h_final_sq : (((2 : ℝ) ^ r)⁻¹) ^ 2 ≤ eps ^ 2 := by
    have hpos : 0 ≤ ((2 : ℝ) ^ r)⁻¹ := by positivity
    nlinarith
  have h_total : u ^ 2 ≤ eps ^ 2 := by
    linarith [hu_sq, h40, h_inv_sq, h_final_sq]
  exact sq_le_sq_of_nonneg hu heps0.le h_total

lemma error_bound_chain (u v eps : ℝ) (r : ℕ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (heps0 : 0 < eps)
    (hinv : 1 / eps ≤ (2 : ℝ) ^ r)
    (hu_sq : u ^ 2 ≤ 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹)
    (hv_sq : v ^ 2 ≤ 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) :
    u + v ≤ eps := by
  have h_sum_sq : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by
    have : 0 ≤ (u - v) ^ 2 := sq_nonneg _
    linarith
  have h_uv : 2 * (u ^ 2 + v ^ 2) ≤ 288 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by linarith
  have h2pow : (2 : ℝ) ^ (2 * r + 9) = ((2 : ℝ) ^ r) ^ 2 * 512 := by
    rw [pow_add, ← pow_mul, mul_comm 2 r, pow_mul]
    norm_num
  have hinv_split : ((2 : ℝ) ^ (2 * r + 9))⁻¹ = (((2 : ℝ) ^ r) ^ 2)⁻¹ * (512 : ℝ)⁻¹ := by
    rw [h2pow, mul_inv]
  have h288 : 288 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ ≤ (((2 : ℝ) ^ r) ^ 2)⁻¹ := by
    rw [hinv_split]
    have : 288 * ((((2 : ℝ) ^ r) ^ 2)⁻¹ * (512 : ℝ)⁻¹) = (288 * (512 : ℝ)⁻¹) * (((2 : ℝ) ^ r) ^ 2)⁻¹ := by ring
    rw [this]
    have hfrac : 288 * (512 : ℝ)⁻¹ ≤ 1 := by norm_num
    have hpos : 0 ≤ (((2 : ℝ) ^ r) ^ 2)⁻¹ := by positivity
    exact mul_le_of_le_one_left hpos hfrac
  have h_inv_sq : (((2 : ℝ) ^ r) ^ 2)⁻¹ = (((2 : ℝ) ^ r)⁻¹) ^ 2 := by rw [inv_pow]
  have h1 : 1 ≤ (2 : ℝ) ^ r * eps := by rwa [div_le_iff₀ heps0] at hinv
  have h2pos : 0 < (2 : ℝ) ^ r := by positivity
  have h_eps_le : ((2 : ℝ) ^ r)⁻¹ ≤ eps := by
    rw [inv_eq_one_div]
    refine (div_le_iff₀ h2pos).mpr ?_
    linarith
  have h_final_sq : (((2 : ℝ) ^ r)⁻¹) ^ 2 ≤ eps ^ 2 := by
    have hpos : 0 ≤ ((2 : ℝ) ^ r)⁻¹ := by positivity
    nlinarith
  have h_total : (u + v) ^ 2 ≤ eps ^ 2 := by
    linarith [h_sum_sq, h_uv, h288, h_inv_sq, h_final_sq]
  exact sq_le_sq_of_nonneg (by linarith) heps0.le h_total

/-! ### Part 5: Top-level theorem solution -/

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ m : ℕ, (n + 1) / 2 ≤ m ∧
        (m : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) +
          C * (1 + Real.log (1 / eps) / Real.log 2) ∧
      ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
        (∃ phi0 phi1 : EuclideanSpace ℂ (Bool × Qubits n),
          IsState phi0 ∧ IsState phi1 ∧
          (∀ z, HasDenominator 2 m (phi0 z)) ∧
          (∀ z, HasDenominator 2 m (phi1 z)) ∧
          frobNorm (householderReflection phi0 * householderReflection phi1 - identityExtension (householderReflection psi)) ≤ eps) ∧
        ((∃ j l : Qubits n, j ≠ l ∧ psi j = 0 ∧ psi l = 0) →
          ∃ phi : EuclideanSpace ℂ (Qubits n), IsState phi ∧
            (∀ z, HasDenominator 2 m (phi z)) ∧
            frobNorm (householderReflection phi - householderReflection psi) ≤ eps) := by
  refine ⟨11, by norm_num, fun n hn eps heps0 heps1 => ?_⟩
  set k := (n + 1) / 2
  set r := Nat.ceil (Real.log (1 / eps) / Real.log 2)
  set m := k + 2 * r + 9
  have hm_ge : k ≤ m := by omega
  have hm_upper : (m : ℝ) ≤ (k : ℝ) + 11 * (1 + Real.log (1 / eps) / Real.log 2) :=
    m_upper_bound n eps heps0 heps1
  refine ⟨m, hm_ge, hm_upper, fun psi hpsi => ⟨?_, ?_⟩⟩

  · -- Clause 1: Two reflections on one extra qubit
    set psi0 := tensorVec (ket false) psi
    set psi1 := tensorVec (ket true) psi
    have hpsi0 : IsState psi0 := isState_tensor_false psi hpsi
    have hpsi1 : IsState psi1 := isState_tensor_true psi hpsi
    obtain ⟨j0, l0, hjl0, hj0, hl0⟩ := tensor_false_two_zeros hn psi
    obtain ⟨j1, l1, hjl1, hj1, hl1⟩ := tensor_true_two_zeros hn psi

    set K : ℝ := (2 : ℝ) ^ k
    have hK : 0 < K := by positivity
    have hmK : K ≤ (2 : ℝ) ^ m := by
      exact pow_le_pow_right₀ (by norm_num) hm_ge

    obtain ⟨phi0, hphi0_state, hphi0_denom, hphi0_dist⟩ :=
      two_zero_approx psi0 hpsi0 j0 l0 hjl0 hj0 hl0 m K hK hmK
    obtain ⟨phi1, hphi1_state, hphi1_denom, hphi1_dist⟩ :=
      two_zero_approx psi1 hpsi1 j1 l1 hjl1 hj1 hl1 m K hK hmK

    refine ⟨phi0, phi1, hphi0_state, hphi1_state, hphi0_denom, hphi1_denom, ?_⟩

    have hcard_bool := card_bool_qubits_le_two_mul_sq n
    have hcomb : K + 4 * (Fintype.card (Bool × Qubits n) : ℝ) / K ≤ 9 * K := by
      calc K + 4 * (Fintype.card (Bool × Qubits n) : ℝ) / K
        _ ≤ K + 4 * (2 * K ^ 2) / K := by
          have : 4 * (Fintype.card (Bool × Qubits n) : ℝ) / K ≤ 4 * (2 * K ^ 2) / K := by
            exact div_le_div_of_nonneg_right (by nlinarith [hcard_bool]) hK.le
          linarith
        _ = 9 * K := by
          have : 4 * (2 * K ^ 2) / K = 8 * K := by
            have : 4 * (2 * K ^ 2) = 8 * K * K := by ring
            rw [this, mul_div_cancel_right₀ _ (ne_of_gt hK)]
          linarith

    have hm_split : m = k + (2 * r + 9) := by omega
    have hpow_m : (2 : ℝ) ^ m = K * (2 : ℝ) ^ (2 * r + 9) := by
      dsimp [K]
      rw [hm_split, pow_add]
    have hinv_m : ((2 : ℝ) ^ m)⁻¹ = K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      rw [hpow_m, mul_inv]
    have hbound_common : ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card (Bool × Qubits n) : ℝ) / K) ≤
        9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      calc ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card (Bool × Qubits n) : ℝ) / K)
        _ ≤ ((2 : ℝ) ^ m)⁻¹ * (9 * K) := mul_le_mul_of_nonneg_left hcomb (by positivity)
        _ = (K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹) * (9 * K) := by rw [hinv_m]
        _ = 9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
          have : (K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹) * (9 * K) =
              (K⁻¹ * K) * (9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) := by ring
          rw [this, inv_mul_cancel₀ (ne_of_gt hK), one_mul]

    have hdist0 : ‖phi0 - psi0‖ ^ 2 ≤ 9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ :=
      hphi0_dist.trans hbound_common
    have hdist1 : ‖phi1 - psi1‖ ^ 2 ≤ 9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ :=
      hphi1_dist.trans hbound_common

    have hU1 : householderReflection phi1 ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ :=
      householder_unitary phi1 hphi1_state
    have hV0 : householderReflection psi0 ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ :=
      householder_unitary psi0 hpsi0

    rw [← householder_prod_tensor_eq psi]
    have h_tri := frobNorm_mul_sub_mul_le
      (householderReflection phi0) (householderReflection phi1)
      (householderReflection psi0) (householderReflection psi1) hU1 hV0

    set u0 := frobNorm (householderReflection phi0 - householderReflection psi0)
    set u1 := frobNorm (householderReflection phi1 - householderReflection psi1)
    have hu0_le : u0 ≤ 2 * Real.sqrt 2 * ‖phi0 - psi0‖ :=
      g64r_main phi0 psi0 hphi0_state hpsi0
    have hu1_le : u1 ≤ 2 * Real.sqrt 2 * ‖phi1 - psi1‖ :=
      g64r_main phi1 psi1 hphi1_state hpsi1

    have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      calc (2 * Real.sqrt 2) ^ 2
        _ = 2 ^ 2 * (Real.sqrt 2) ^ 2 := mul_pow _ _ _
        _ = 4 * 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
        _ = 8 := by norm_num

    have hu0_sq : u0 ^ 2 ≤ 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      have h1 := sq_le_sq_of_le (norm_nonneg _) hu0_le
      have h2 : (2 * Real.sqrt 2 * ‖phi0 - psi0‖) ^ 2 = 8 * ‖phi0 - psi0‖ ^ 2 := by
        rw [mul_pow, h8]
      rw [h2] at h1
      calc u0 ^ 2
        _ ≤ 8 * ‖phi0 - psi0‖ ^ 2 := h1
        _ ≤ 8 * (9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) := mul_le_mul_of_nonneg_left hdist0 (by norm_num)
        _ = 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by ring

    have hu1_sq : u1 ^ 2 ≤ 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      have h1 := sq_le_sq_of_le (norm_nonneg _) hu1_le
      have h2 : (2 * Real.sqrt 2 * ‖phi1 - psi1‖) ^ 2 = 8 * ‖phi1 - psi1‖ ^ 2 := by
        rw [mul_pow, h8]
      rw [h2] at h1
      calc u1 ^ 2
        _ ≤ 8 * ‖phi1 - psi1‖ ^ 2 := h1
        _ ≤ 8 * (9 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) := mul_le_mul_of_nonneg_left hdist1 (by norm_num)
        _ = 72 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by ring

    have h_inv_eps := two_pow_r_ge_inv_eps eps heps0 heps1
    have h_chain := error_bound_chain u0 u1 eps r (norm_nonneg _) (norm_nonneg _) heps0 h_inv_eps hu0_sq hu1_sq
    exact h_tri.trans h_chain

  · -- Clause 2: One reflection when two distinct coordinates vanish
    rintro ⟨j, l, hjl, hj, hl⟩
    set K : ℝ := (2 : ℝ) ^ k
    have hK : 0 < K := by positivity
    have hmK : K ≤ (2 : ℝ) ^ m := by
      exact pow_le_pow_right₀ (by norm_num) hm_ge

    obtain ⟨phi, hphi_state, hphi_denom, hphi_dist⟩ :=
      two_zero_approx psi hpsi j l hjl hj hl m K hK hmK
    refine ⟨phi, hphi_state, hphi_denom, ?_⟩

    have hcard := card_qubits_le_sq n
    have hcomb : K + 4 * (Fintype.card (Qubits n) : ℝ) / K ≤ 5 * K := by
      calc K + 4 * (Fintype.card (Qubits n) : ℝ) / K
        _ ≤ K + 4 * (K ^ 2) / K := by
          have : 4 * (Fintype.card (Qubits n) : ℝ) / K ≤ 4 * (K ^ 2) / K := by
            exact div_le_div_of_nonneg_right (by nlinarith [hcard]) hK.le
          linarith
        _ = 5 * K := by
          have : 4 * (K ^ 2) / K = 4 * K := by
            have : 4 * (K ^ 2) = 4 * K * K := by ring
            rw [this, mul_div_cancel_right₀ _ (ne_of_gt hK)]
          linarith

    have hm_split : m = k + (2 * r + 9) := by omega
    have hpow_m : (2 : ℝ) ^ m = K * (2 : ℝ) ^ (2 * r + 9) := by
      dsimp [K]
      rw [hm_split, pow_add]
    have hinv_m : ((2 : ℝ) ^ m)⁻¹ = K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      rw [hpow_m, mul_inv]
    have hbound_common : ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card (Qubits n) : ℝ) / K) ≤
        5 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      calc ((2 : ℝ) ^ m)⁻¹ * (K + 4 * (Fintype.card (Qubits n) : ℝ) / K)
        _ ≤ ((2 : ℝ) ^ m)⁻¹ * (5 * K) := mul_le_mul_of_nonneg_left hcomb (by positivity)
        _ = (K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹) * (5 * K) := by rw [hinv_m]
        _ = 5 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
          have : (K⁻¹ * ((2 : ℝ) ^ (2 * r + 9))⁻¹) * (5 * K) =
              (K⁻¹ * K) * (5 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) := by ring
          rw [this, inv_mul_cancel₀ (ne_of_gt hK), one_mul]

    have hdist : ‖phi - psi‖ ^ 2 ≤ 5 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ :=
      hphi_dist.trans hbound_common

    set u := frobNorm (householderReflection phi - householderReflection psi)
    have hu_le : u ≤ 2 * Real.sqrt 2 * ‖phi - psi‖ :=
      g64r_main phi psi hphi_state hpsi

    have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      calc (2 * Real.sqrt 2) ^ 2
        _ = 2 ^ 2 * (Real.sqrt 2) ^ 2 := mul_pow _ _ _
        _ = 4 * 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
        _ = 8 := by norm_num

    have hu_sq : u ^ 2 ≤ 40 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by
      have h1 := sq_le_sq_of_le (norm_nonneg _) hu_le
      have h2 : (2 * Real.sqrt 2 * ‖phi - psi‖) ^ 2 = 8 * ‖phi - psi‖ ^ 2 := by
        rw [mul_pow, h8]
      rw [h2] at h1
      calc u ^ 2
        _ ≤ 8 * ‖phi - psi‖ ^ 2 := h1
        _ ≤ 8 * (5 * ((2 : ℝ) ^ (2 * r + 9))⁻¹) := mul_le_mul_of_nonneg_left hdist (by norm_num)
        _ = 40 * ((2 : ℝ) ^ (2 * r + 9))⁻¹ := by ring

    have h_inv_eps := two_pow_r_ge_inv_eps eps heps0 heps1
    exact single_error_bound_chain u eps r (norm_nonneg _) heps0 h_inv_eps hu_sq

end
