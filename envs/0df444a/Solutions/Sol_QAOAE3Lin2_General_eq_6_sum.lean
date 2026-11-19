-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_6_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:31:12.917015+00:00
-- url     : https://prove2.me/submissions/1dfa2c73-7840-4a1f-9142-e80921e9e882

import Definitions.Def_QAOAE3Lin2_General_Setting

open QAlgorithms
open QAOAE3Lin2.General

private def flipBits {n : ℕ} (x : Qubits n) : Qubits n := fun v => !(x v)

private lemma flipBits_involutive {n : ℕ} : Function.Involutive (@flipBits n) := by
  intro x; ext v; simp [flipBits]

private lemma satCount_flipBits {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (rhs : Fin m → Bool) (x : Qubits n) :
    satCount tri rhs (flipBits x) = (m : ℝ) - satCount tri rhs x := by
  unfold satCount flipBits
  have hpart : (Finset.univ.filter fun i : Fin m =>
      (xor (xor (!(x (tri i).1)) (!(x (tri i).2.1))) (!(x (tri i).2.2))) = rhs i) =
      (Finset.univ.filter fun i : Fin m =>
      ¬ ((xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x (tri i).1 <;> cases x (tri i).2.1 <;> cases x (tri i).2.2 <;> cases rhs i <;> decide
  rw [hpart]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m)))
    (p := fun i => (xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hcast : ((Finset.univ.filter fun i : Fin m =>
      (xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i).card : ℝ) +
      ((Finset.univ.filter fun i : Fin m =>
      ¬ ((xor (xor (x (tri i).1) (x (tri i).2.1)) (x (tri i).2.2)) = rhs i)).card : ℝ) =
      (m : ℝ) := by exact_mod_cast hsum
  linarith

private noncomputable def flipMat (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  fun x y => if x = flipBits y then 1 else 0

private lemma flipMat_sq (n : ℕ) : flipMat n * flipMat n = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [flipMat]
  rw [Finset.sum_eq_single (flipBits y)]
  · by_cases h : x = y
    · subst h; simp [flipBits_involutive x]
    · have hne : x ≠ flipBits (flipBits y) := by simpa [flipBits_involutive y] using h
      simp [h, hne]
  · intro z _ hz
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma flipMat_conj (n : ℕ) (A : Matrix (Qubits n) (Qubits n) ℂ) (x y : Qubits n) :
    (flipMat n * A * flipMat n) x y = A (flipBits x) (flipBits y) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipBits x)]
  · simp only [flipMat, flipBits_involutive x, ↓reduceIte, one_mul]
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (flipBits y)]
    · simp [flipMat, flipBits_involutive y]
    · intro z _ hz
      simp [flipMat, hz]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro z _ hz
    have hne : x ≠ flipBits z := fun h => hz (by rw [h, flipBits_involutive z])
    simp [flipMat, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma flipMat_pauliX (n : ℕ) (q : Fin n) (x y : Qubits n) :
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli q Stabilizer.Pauli.X)
      (flipBits x) (flipBits y) =
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli q Stabilizer.Pauli.X) x y := by
  dsimp only [Stabilizer.CliffordOp.mat]
  unfold embedOp
  simp only [Matrix.of_apply]
  split_ifs
  · simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.wire1, Stabilizer.Pauli.mat, pauliX,
      flipBits, Matrix.submatrix_apply]
    cases x q <;> cases y q <;> simp
  · exfalso; simp_all [flipBits]
  · exfalso; simp_all [flipBits]
  · rfl

private lemma flipMat_mixer (n : ℕ) :
    flipMat n * qaoaMixer n * flipMat n = qaoaMixer n := by
  ext x y
  rw [flipMat_conj]
  simp only [qaoaMixer, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun q _ => flipMat_pauliX n q x y

private lemma flipMat_uniform (n : ℕ) :
    act (flipMat n) (uniformState (Qubits n)) = uniformState (Qubits n) := by
  ext x
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, uniformState]
  rw [Finset.sum_eq_single (flipBits x)]
  · simp [flipMat, flipBits_involutive x]
  · intro y _ hy
    have hne : x ≠ flipBits y := fun h => hy (by rw [h, flipBits_involutive y])
    simp [flipMat, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma matrix_exp_eq_linfty {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    NormedSpace.exp M =
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      NormedSpace.exp M) := by
  have ha :
      (letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
      HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M)) := by
    letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
    have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
    have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
      rw [← summable_nat_add_iff 1]
      refine Summable.of_norm_bounded
        ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
      simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      exact hpow_norm k
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    exact hs.hasSum
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]

private lemma matrix_exp_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasSum (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) (NormedSpace.exp M) := by
  rw [matrix_exp_eq_linfty M]
  refine (Pi.hasSum (f := fun k (i j : ι) => ((Nat.factorial k : ℂ)⁻¹ • M ^ k) i j)).mpr fun i => ?_
  refine (Pi.hasSum (f := fun k (j : ι) => ((Nat.factorial k : ℂ)⁻¹ • M ^ k) i j)).mpr fun j => ?_
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow_norm : ∀ k : ℕ, ‖M ^ (k + 1)‖ ≤ ‖M‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • M ^ k) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial ‖M‖).comp_injective Nat.succ_injective) fun k => ?_
    simp only [Function.comp_apply, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact hpow_norm k
  let evalIJ : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcont : Continuous evalIJ := LinearMap.continuous_of_finiteDimensional evalIJ
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  exact hs.hasSum.map evalIJ.toAddMonoidHom hcont

private lemma exp_conj_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U * U = 1) (A : Matrix ι ι ℂ) :
    U * NormedSpace.exp A * U = NormedSpace.exp (U * A * U) := by
  have hpow : ∀ k : ℕ, (U * A * U) ^ k = U * A ^ k * U := by
    intro k
    induction k with
    | zero => simp [hU]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      congr 1; congr 1
      rw [← Matrix.mul_assoc U U, hU, one_mul]
  let mulLR : Matrix ι ι ℂ →+ Matrix ι ι ℂ :=
    { toFun := fun X => U * X * U
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hcont : Continuous mulLR :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h1 := (matrix_exp_hasSum A).map mulLR hcont
  change HasSum (fun k => mulLR ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) (mulLR (NormedSpace.exp A)) at h1
  have hterm : (fun k : ℕ => mulLR ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) =
      (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • (U * A * U) ^ k) := by
    ext k
    simp only [mulLR, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hpow k, Matrix.smul_mul, Matrix.mul_smul]
  rw [hterm] at h1
  exact h1.unique (matrix_exp_hasSum (U * A * U))

private lemma matrix_exp_add_of_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B := by
  rw [matrix_exp_eq_linfty (A + B), matrix_exp_eq_linfty A, matrix_exp_eq_linfty B]
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_add_of_commute h

private lemma exp_skew_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Matrix.conjTranspose A = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar_exp : Matrix.conjTranspose (NormedSpace.exp A) = NormedSpace.exp (-A) := by
    have h1 := (matrix_exp_hasSum A).star
    have hterm : (fun k : ℕ => star ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) =
        (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • (-A) ^ k) := by
      ext k
      rw [star_smul, star_pow, Matrix.star_eq_conjTranspose, hA, star_inv₀, star_natCast]
    rw [hterm] at h1
    rw [← Matrix.star_eq_conjTranspose]
    exact h1.unique (matrix_exp_hasSum (-A))
  rw [← Matrix.star_eq_conjTranspose] at hstar_exp
  have hexp := matrix_exp_add_of_commute (Commute.neg_left rfl : Commute (-A) A)
  rw [hstar_exp, ← hexp, neg_add_cancel, NormedSpace.exp_zero]

private lemma mixer_hermitian (n : ℕ) : Matrix.conjTranspose (qaoaMixer n) = qaoaMixer n := by
  ext x y
  dsimp only [qaoaMixer]
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only [Stabilizer.CliffordOp.mat]
  unfold embedOp
  simp only [Matrix.of_apply]
  rw [apply_ite Star.star]
  simp only [star_zero]
  split_ifs
  · simp only [Gate.ofMatrix1, Function.comp_apply, Stabilizer.wire1, Stabilizer.Pauli.mat, pauliX,
      Matrix.submatrix_apply]
    cases x q <;> cases y q <;> simp
  · exfalso; simp_all [eq_comm]
  · exfalso; simp_all [eq_comm]
  · rfl

private lemma prob_sum_eq_one {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : ‖ψ‖ = 1) :
    ∑ x : Qubits n, prob ψ x = 1 := by
  have hp : ∀ x : Qubits n, prob ψ x = ‖ψ x‖ ^ 2 := by
    intro x
    simp [prob, ket, EuclideanSpace.inner_single_left]
  simp_rw [hp]
  rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]

private lemma exp_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix ι ι ℂ)) = Complex.exp c • (1 : Matrix ι ι ℂ) := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := Matrix ι ι ℂ), Complex.exp_eq_exp_ℂ,
      NormedSpace.exp_eq_tsum (𝕂 := ℂ) (𝔸 := ℂ)]
  have hterm : ∀ k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (c • (1 : Matrix ι ι ℂ)) ^ k =
      ((Nat.factorial k : ℂ)⁻¹ • c ^ k) • (1 : Matrix ι ι ℂ) := by
    intro k
    rw [smul_pow, one_pow, smul_smul]
    rfl
  simp_rw [hterm]
  have hs : Summable (fun k : ℕ => (Nat.factorial k : ℂ)⁻¹ • c ^ k) := by
    refine Summable.of_norm ?_
    simpa [smul_eq_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_pow, div_eq_inv_mul]
      using Real.summable_pow_div_factorial ‖c‖
  exact (hs.hasSum.smul_const (1 : Matrix ι ι ℂ)).tsum_eq

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) :
    expSat tri rhs γ β = (m : ℝ) / 2 + ∑ i, (1 / 2) * sgn rhs i * corr tri rhs i γ β := by
  have hunit : ‖qaoaState1 tri rhs γ β‖ = 1 := by
    unfold qaoaState1
    have hU_unit : qaoaUnitary (satCount tri rhs) 1 (fun _ => β) (fun _ => γ) ∈
        Matrix.unitaryGroup (Qubits n) ℂ := by
      simp only [qaoaUnitary, orderedProd, List.ofFn_succ, List.ofFn_zero,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      refine Submonoid.mul_mem _ (exp_skew_unitary _ ?_) (exp_skew_unitary _ ?_)
      · rw [Matrix.conjTranspose_smul, mixer_hermitian n]
        simp [Complex.conj_I]
      · rw [Matrix.conjTranspose_smul]
        have hH : Matrix.conjTranspose (problemHamiltonian (satCount tri rhs)) =
            problemHamiltonian (satCount tri rhs) := by
          ext x y
          simp only [Matrix.conjTranspose_apply, problemHamiltonian, Matrix.diagonal_apply]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
        rw [hH]
        simp [Complex.conj_I]
    rw [act_norm_of_mem_unitaryGroup hU_unit, ← Real.sqrt_sq (norm_nonneg _),
        EuclideanSpace.norm_sq_eq]
    simp [uniformState]
  have hprob1 : ∑ x : Qubits n, prob (qaoaState1 tri rhs γ β) x = 1 :=
    prob_sum_eq_one _ hunit
  have hsat : ∀ x : Qubits n, satCount tri rhs x =
      ∑ i : Fin m, ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
        (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) := by
    intro x
    unfold satCount
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [sgn, spin]
    cases x (tri i).1 <;> cases x (tri i).2.1 <;> cases x (tri i).2.2 <;> cases rhs i <;> norm_num
  simp_rw [expSat, hsat, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ i : Fin m,
      (∑ x : Qubits n, prob (qaoaState1 tri rhs γ β) x *
        ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
          (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2))) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i * corr tri rhs i γ β := by
    intro i
    have hsplit : ∀ x : Qubits n,
        prob (qaoaState1 tri rhs γ β) x *
          ((1 / 2 : ℝ) + (1 / 2 : ℝ) * sgn rhs i *
            (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) =
        (1 / 2 : ℝ) * prob (qaoaState1 tri rhs γ β) x +
          (1 / 2 : ℝ) * sgn rhs i * (prob (qaoaState1 tri rhs γ β) x *
            (spin x (tri i).1 * spin x (tri i).2.1 * spin x (tri i).2.2)) := by
      intro x; ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hprob1, corr]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
  ring
