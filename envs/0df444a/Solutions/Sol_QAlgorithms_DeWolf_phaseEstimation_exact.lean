-- Prove2me | solution 1 for QAlgorithms.DeWolf.phaseEstimation_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:37:48.478413+00:00
-- url     : https://prove2.me/submissions/790d5f11-4316-45d1-8ac0-222562ecba15

import Definitions.Def_QAlgorithms_Defs_Fourier

open QAlgorithms
open scoped ComplexConjugate

private lemma act_mul' {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : act (A * B) ψ = act A (act B ψ) := by
  ext i
  exact (congrFun (Matrix.mulVec_mulVec (WithLp.ofLp ψ) A B) i).symm

private lemma act_smul' {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (ψ : EuclideanSpace ℂ ι) : act A (c • ψ) = c • act A ψ := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

private lemma act_tensor' {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ κ) :
    act (Matrix.kronecker A (1 : Matrix κ κ ℂ)) (tensorVec v w) =
      tensorVec (act A v) w := by
  ext ⟨i,j⟩
  simp [act, tensorVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, mul_assoc]

private lemma act_ket' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (j i : ι) : act A (ket j) i = A i j := by
  simp [act, ket]

private lemma control_tensor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (U : Matrix κ κ ℂ) (v : EuclideanSpace ℂ (Qubits n))
    (w : EuclideanSpace ℂ κ) (i : Qubits n) (j : κ) :
    act (controlledPower n U) (tensorVec v w) (i,j) =
      v i * act (U ^ bitsToNat i) w j := by
  simp [act, controlledPower, tensorVec, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm]

private lemma eigen_pow {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ κ) (c : ℂ)
    (hc : act U ψ = c • ψ) (r : ℕ) : act (U ^ r) ψ = c ^ r • ψ := by
  induction r with
  | zero => ext i; simp [act]
  | succ r ih =>
    rw [pow_succ', act_mul', ih, act_smul', hc, smul_smul, pow_succ]

private lemma qft_norm (n : ℕ) (i j : Qubits n) :
    star ((qftQubits n) i j) * (qftQubits n) i j = (2 ^ n : ℂ)⁻¹ := by
  have hpos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hs : (Real.sqrt (2 ^ n) : ℂ) ^ 2 = (2 ^ n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hpos.le
  simp only [qftQubits, Matrix.submatrix_apply, qftMatrix, Matrix.of_apply, Nat.cast_pow, Nat.cast_ofNat]
  rw [star_div₀, ← mul_div_mul_comm]
  change conj (Complex.exp _) * Complex.exp _ / _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have hz : star (2 * (Real.pi : ℂ) * Complex.I *
      ((↑(bitsEquivFin n i) * ↑(bitsEquivFin n j) : ℕ) : ℂ) / (2 ^ n : ℂ)) +
      2 * (Real.pi : ℂ) * Complex.I *
      ((↑(bitsEquivFin n i) * ↑(bitsEquivFin n j) : ℕ) : ℂ) / (2 ^ n : ℂ) = 0 := by
    simp [Nat.cast_mul]
    ring
  change Complex.exp (star _ + _) / _ = _
  rw [hz, Complex.exp_zero]
  simp only [Complex.star_def, Complex.conj_ofReal]
  norm_cast at hs ⊢
  simpa [pow_two] using congrArg (fun z : ℝ => z⁻¹) hs

theorem solution {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (U : Matrix κ κ ℂ) (_hU : U ∈ Matrix.unitaryGroup κ ℂ)
    (ψ : EuclideanSpace ℂ κ) (hψ : IsState ψ)
    (ϕ : ℝ) (_hϕ0 : 0 ≤ ϕ) (hϕ1 : ϕ < 1)
    (heig : act U ψ = Complex.exp (2 * Real.pi * Complex.I * ϕ) • ψ)
    (k : ℕ) (hk : (2 : ℝ) ^ n * ϕ = k) :
    act (controlledPower n U * Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ))
        (tensorVec (zeroKet n) ψ) =
      tensorVec (act (qftQubits n) (ket (natToBits n k))) ψ ∧
    marginalFst (phaseEstimationState n U ψ) (natToBits n k) = 1 := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  have hklt : k < 2 ^ n := by
    have : (k : ℝ) < (2 : ℝ) ^ n := by nlinarith
    exact_mod_cast this
  have hbits : bitsToNat (natToBits n k) = k := by
    rw [← bitsEquivFin_apply]
    simp [natToBits, Nat.mod_eq_of_lt hklt]
  have hz : bitsToNat (fun _ : Fin n => false) = 0 := by simp [bitsToNat]
  have hphase : (ϕ : ℂ) = (k : ℂ) / (2 ^ n : ℂ) := by
    have hk' : (2 ^ n : ℂ) * (ϕ : ℂ) = k := by exact_mod_cast hk
    apply (eq_div_iff (pow_ne_zero _ (by norm_num) : (2 ^ n : ℂ) ≠ 0)).2
    simpa [mul_comm] using hk'
  have hfirst : act (controlledPower n U * Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ))
        (tensorVec (zeroKet n) ψ) =
      tensorVec (act (qftQubits n) (ket (natToBits n k))) ψ := by
    rw [act_mul', act_tensor']
    ext ⟨i,j⟩
    rw [control_tensor, eigen_pow U ψ _ heig]
    simp only [tensorVec, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
      zeroKet, act_ket', qftQubits, Matrix.submatrix_apply, qftMatrix,
      Matrix.of_apply, bitsEquivFin_apply, hz, hbits,
      Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero]
    rw [← Complex.exp_nat_mul, hphase]
    push_cast
    have hexp : (bitsToNat i : ℂ) * (2 * Real.pi * Complex.I * ((k : ℂ) / 2 ^ n)) =
        2 * Real.pi * Complex.I * ((bitsToNat i : ℂ) * k) / 2 ^ n := by ring
    rw [hexp]
    ring
  refine ⟨hfirst, ?_⟩
  have hcoord (j : κ) : phaseEstimationState n U ψ (natToBits n k,j) = ψ j := by
    unfold phaseEstimationState
    rw [Matrix.mul_assoc, act_mul', hfirst, act_tensor']
    simp only [tensorVec, PiLp.toLp_apply]
    have hf : act (star (qftQubits n)) (act (qftQubits n) (ket (natToBits n k)))
        (natToBits n k) = 1 := by
      simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
        Matrix.star_apply]
      have he : ∀ i : Qubits n,
          star (qftQubits n i (natToBits n k)) *
              (∑ x, qftQubits n i x * (WithLp.ofLp (ket (natToBits n k))) x) =
          (2 ^ n : ℂ)⁻¹ := by
        intro i
        change star (qftQubits n i (natToBits n k)) *
            act (qftQubits n) (ket (natToBits n k)) i = _
        rw [act_ket', qft_norm]
      simp_rw [he]
      simp [Qubits, Fintype.card_fin, Fintype.card_bool]
    rw [hf, one_mul]
  simp only [marginalFst, prob, ket, EuclideanSpace.inner_single_left, map_one,
    one_mul, hcoord]
  have hn := EuclideanSpace.norm_sq_eq ψ
  rw [hψ, one_pow] at hn
  exact hn.symm

