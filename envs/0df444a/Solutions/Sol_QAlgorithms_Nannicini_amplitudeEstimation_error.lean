-- Prove2me | solution 1 for QAlgorithms.Nannicini.amplitudeEstimation_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:02:00.480283+00:00
-- url     : https://prove2.me/submissions/ad10b969-fe04-4d1f-9696-d299be205e80

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
import Theorems.Thm_QAlgorithms_Nannicini_groverOperator_eigenstates
import Theorems.Thm_QAmpEst_Est_theorem_11_eight_over_pi_sq
set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate

private lemma vo_fourier_unitary (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hw : IsPrimitiveRoot w N := Complex.isPrimitiveRoot_exp N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hs : (Real.sqrt N : ℂ) ^ 2 = N := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  have hw_norm : ‖w‖ = 1 := hw.norm'_eq_one hN
  have hw_star (j : ℕ) : star (w ^ j) = (w ^ j)⁻¹ := by
    exact (Complex.inv_eq_conj (by simp [norm_pow, hw_norm])).symm
  have he (a b : Fin N) : qftMatrix N a b = w ^ ((a : ℕ) * (b : ℕ)) / (Real.sqrt N : ℂ) := by
    simp only [qftMatrix, Matrix.of_apply, w, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  apply Matrix.mem_unitaryGroup_iff'.2
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, he, star_div₀,
    Complex.star_def, Complex.conj_ofReal]
  have hp (j : Fin N) :
      conj (w ^ ((j : ℕ) * (a : ℕ))) / (Real.sqrt N : ℂ) *
          (w ^ ((j : ℕ) * (b : ℕ)) / (Real.sqrt N : ℂ)) =
        ((w ^ (b : ℕ) / w ^ (a : ℕ)) ^ (j : ℕ)) / (N : ℂ) := by
    rw [← Complex.star_def, hw_star]
    rw [div_mul_div_comm, ← pow_two, hs, div_pow]
    simp only [← pow_mul]
    ring
  simp_rw [hp]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range]
  by_cases hab : a = b
  · subst b
    simp [div_self (pow_ne_zero _ (hw.ne_zero hN)), hn]
  · have hr : w ^ (b : ℕ) / w ^ (a : ℕ) ≠ 1 := by
      intro hr
      have hh := (div_eq_one_iff_eq (pow_ne_zero _ (hw.ne_zero hN))).1 hr
      have hh' := hw.pow_inj b.isLt a.isLt hh
      exact hab (Fin.ext hh'.symm)
    have hrN : (w ^ (b : ℕ) / w ^ (a : ℕ)) ^ N = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm (b : ℕ) N,
        mul_comm (a : ℕ) N, pow_mul, pow_mul, hw.pow_eq_one]
      simp
    rw [geom_sum_eq hr, hrN]
    simp [hab]

private lemma vo_qubits_unitary (m : ℕ) :
    qftQubits m ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.2
  simp only [qftQubits, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose,
    Unitary.mul_star_self_of_mem (vo_fourier_unitary (2 ^ m) (by positivity)),
    Matrix.submatrix_one_equiv]

private lemma vo_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) : act (A * B) v = act A (act B v) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma vo_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act (star A) y) = inner ℂ (act A x) y := by
  change inner ℂ x (Matrix.toEuclideanLin (star A) y) =
    inner ℂ (Matrix.toEuclideanLin A x) y
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_right _ _ _

private lemma vo_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ι) : inner ℂ (act A x) (act A y) = inner ℂ x y := by
  rw [← vo_adjoint, ← vo_mul, Unitary.star_mul_self_of_mem hA]
  simp [act]

private lemma ip_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (c : ℂ) (x : EuclideanSpace ℂ ι) : act A (c • x) = c • act A x := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

private lemma ip_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ x (act A y) = inner ℂ (act (star A) x) y := by
  change inner ℂ x (Matrix.toEuclideanLin A y) =
    inner ℂ (Matrix.toEuclideanLin (star A) x) y
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_left _ _ _).symm

private lemma ip_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (c : ℂ)
    (hc : act U v = c • v) (r : ℕ) : act (U ^ r) v = c ^ r • v := by
  induction r with
  | zero => ext i; simp [act]
  | succ r ih => rw [pow_succ', vo_mul, ih, ip_smul, hc, smul_smul, pow_succ]

private lemma ip_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U x (a,b)) : EuclideanSpace ℂ ι) =
      ∑ k : Qubits m, ((star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k)) • act (U ^ bitsToNat k) x := by
  have ht (A : Matrix (Qubits m) (Qubits m) ℂ) (v : EuclideanSpace ℂ (Qubits m)) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) (tensorVec v x) =
        tensorVec (act A v) x := by
    ext ⟨i,j⟩
    simp [act, tensorVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, Finset.sum_mul, mul_assoc]
  have hf (A : Matrix (Qubits m) (Qubits m) ℂ)
      (w : EuclideanSpace ℂ (Qubits m × ι)) (i : Qubits m) (j : ι) :
      act (Matrix.kronecker A (1 : Matrix ι ι ℂ)) w (i,j) =
        ∑ k, A i k * w (k,j) := by
    simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  have hp (v : EuclideanSpace ℂ (Qubits m)) (i : Qubits m) (j : ι) :
      act (controlledPower m U) (tensorVec v x) (i,j) =
        v i * act (U ^ bitsToNat i) x j := by
    simp [act, controlledPower, tensorVec, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm]
  ext b
  change phaseEstimationState m U x (a,b) = _
  unfold phaseEstimationState
  rw [vo_mul, vo_mul, ht, hf]
  simp_rw [hp]
  simp [mul_assoc]

private lemma ip_slice_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (c : ℂ)
    (hc : act U v = c • v) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U v (a,b)) : EuclideanSpace ℂ ι) =
      (∑ k : Qubits m, (star (qftQubits m) a k) *
        (act (qftQubits m) (zeroKet m) k) * c ^ bitsToNat k) • v := by
  rw [ip_slice]
  simp_rw [ip_pow U v c hc, smul_smul]
  rw [Finset.sum_smul]

private lemma ip_event_slices {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x : EuclideanSpace ℂ (ι × κ))
    (P : ι → Prop) [DecidablePred P] :
    probEvent x (fun z => P z.1) =
      ∑ a ∈ Finset.univ.filter P,
        ‖(WithLp.toLp 2 (fun b => x (a,b)) : EuclideanSpace ℂ κ)‖ ^ 2 := by
  classical
  simp only [probEvent, Finset.sum_filter, prob, ket, EuclideanSpace.inner_single_left]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp only [h, ite_true]
    simpa using (EuclideanSpace.norm_sq_eq
      (WithLp.toLp 2 (fun b => x (a,b)) : EuclideanSpace ℂ κ)).symm
  · simp [h]

private lemma sin_sq_error (θ d : ℝ) :
    |Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2| ≤
      2 * |d| * |Real.sin θ * Real.cos θ| + |d| ^ 2 := by
  have ht := Real.sin_sq_add_cos_sq θ
  have hd := Real.sin_sq_add_cos_sq d
  have hid : Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2 =
      (Real.sin θ * Real.cos θ) * Real.sin (2 * d) +
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) * Real.sin d ^ 2 := by
    rw [Real.sin_add, Real.sin_two_mul]
    nlinarith [sq_nonneg (Real.sin θ * Real.sin d)]
  have hc : |Real.cos θ ^ 2 - Real.sin θ ^ 2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  have hsin : |Real.sin (2 * d)| ≤ 2 * |d| := by
    simpa [abs_mul] using Real.abs_sin_le_abs (x := 2 * d)
  have hsq : Real.sin d ^ 2 ≤ |d| ^ 2 := by
    have h := Real.abs_sin_le_abs (x := d)
    simpa only [← sq, sq_abs] using
      mul_self_le_mul_self (abs_nonneg (Real.sin d)) h
  rw [hid]
  calc
    _ ≤ |(Real.sin θ * Real.cos θ) * Real.sin (2 * d)| +
        |(Real.cos θ ^ 2 - Real.sin θ ^ 2) * Real.sin d ^ 2| := abs_add_le _ _
    _ = |Real.sin θ * Real.cos θ| * |Real.sin (2 * d)| +
        |Real.cos θ ^ 2 - Real.sin θ ^ 2| * Real.sin d ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
    _ ≤ |Real.sin θ * Real.cos θ| * (2 * |d|) + 1 * |d| ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsin (abs_nonneg _))
        (mul_le_mul hc hsq (sq_nonneg _) (by norm_num))
    _ = _ := by ring

private lemma pf_distance (x y : ℝ) : QAmpEst.Est.circDist x y = circDist x y := by
  unfold QAmpEst.Est.circDist circDist
  apply le_antisymm
  · apply ciInf_le_of_le (show BddBelow (Set.range fun z : ℤ => |(z : ℝ) + y - x|) from
      ⟨0, by rintro _ ⟨z,rfl⟩; exact abs_nonneg _⟩) (round (x-y))
    rw [show (round (x-y) : ℝ) + y - x = -((x-y) - round (x-y)) by ring, abs_neg]
  · apply le_ciInf
    intro z
    simpa only [show (z : ℝ) + y - x = -((x-y) - z) by ring, abs_neg] using round_le (x-y) z

private lemma pf_matrix (N : ℕ) :
    ShorAlgorithms.Shared.fourierMatrix N = qftMatrix N := by
  ext a b
  simp [ShorAlgorithms.Shared.fourierMatrix, qftMatrix, Nat.cast_mul, div_eq_mul_inv]
  ring

private lemma pf_prob (m : ℕ) (ω : ℝ) (a : Qubits m) :
    QAmpEst.Est.phaseProb (2 ^ m) ω (bitsEquivFin m a) =
      prob (aeVartheta m (Real.pi * ω)) a := by
  have hstate (k : Qubits m) :
      QAmpEst.Est.stateS (2 ^ m) ω (bitsEquivFin m k) =
        Complex.exp (2 * Complex.I * ((Real.pi * ω : ℝ) : ℂ) * (bitsToNat k : ℂ)) *
          ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ) := by
    simp only [QAmpEst.Est.stateS, bitsEquivFin_apply, Nat.cast_pow, Nat.cast_ofNat,
      Complex.ofReal_mul, div_eq_mul_inv, Complex.ofReal_inv]
    congr 2
    ring
  have hvec : (QAmpEst.Est.qftInv (2 ^ m)).mulVec
      (QAmpEst.Est.stateS (2 ^ m) ω) (bitsEquivFin m a) = aeVartheta m (Real.pi * ω) a := by
    simp only [aeVartheta, act, Matrix.mulVec, dotProduct, PiLp.toLp_apply,
      QAmpEst.Est.qftInv, pf_matrix, qftQubits, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.submatrix_apply]
    rw [← (bitsEquivFin m).sum_comp]
    simp_rw [hstate]
  simp only [QAmpEst.Est.phaseProb, hvec, prob, ket, EuclideanSpace.inner_single_left,
    Complex.normSq_eq_norm_sq, map_one, one_mul]

private lemma pf_initial (m : ℕ) (k : Qubits m) :
    act (qftQubits m) (zeroKet m) k = ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ) := by
  simp [act, zeroKet, ket, qftQubits, qftMatrix, bitsEquivFin_apply,
    bitsToNat, Matrix.mulVec, dotProduct]

private lemma pf_eigen_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (ω : ℝ)
    (he : act U v = Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ)) • v) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U v (a,b)) : EuclideanSpace ℂ ι) =
      (aeVartheta m (Real.pi * ω) a) • v := by
  rw [ip_slice_eigen _ _ _ _ he]
  congr 1
  simp only [pf_initial]
  simp only [aeVartheta, act, Matrix.mulVec, dotProduct, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.exp_nat_mul]
  have heq : (bitsToNat k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (ω : ℂ)) =
      2 * Complex.I * ((Real.pi * ω : ℝ) : ℂ) * (bitsToNat k : ℂ) := by push_cast; ring
  rw [heq]
  ring

private lemma pf_total (m : ℕ) (ω : ℝ) :
    (∑ a : Qubits m, prob (aeVartheta m (Real.pi * ω)) a) = 1 := by
  have hnorm (A : Matrix (Qubits m) (Qubits m) ℂ)
      (hA : A ∈ Matrix.unitaryGroup (Qubits m) ℂ)
      (v : EuclideanSpace ℂ (Qubits m)) : ‖act A v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), vo_inner A hA]
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) v).symm
  have hcoef (k : Qubits m) :
      ‖Complex.exp (2 * Complex.I * ((Real.pi * ω : ℝ) : ℂ) * (bitsToNat k : ℂ)) *
          ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ)‖ ^ 2 = ((Real.sqrt ((2 : ℝ) ^ m))⁻¹) ^ 2 := by
    rw [norm_mul]
    have he : 2 * Complex.I * ((Real.pi * ω : ℝ) : ℂ) * (bitsToNat k : ℂ) =
        ((2 * (Real.pi * ω) * (bitsToNat k : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
    simp [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hc : Fintype.card (Qubits m) = 2 ^ m := by
    simpa using Fintype.card_congr (bitsEquivFin m)
  calc
    _ = ‖aeVartheta m (Real.pi * ω)‖ ^ 2 := by
      simp only [prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
      exact (EuclideanSpace.norm_sq_eq (aeVartheta m (Real.pi * ω))).symm
    _ = (2 : ℝ) ^ m * ((Real.sqrt ((2 : ℝ) ^ m))⁻¹) ^ 2 := by
      rw [aeVartheta, hnorm (star (qftQubits m)) (Unitary.star_mem (vo_qubits_unitary m)), EuclideanSpace.norm_sq_eq]
      simp only [PiLp.toLp_apply, hcoef, Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
    _ = 1 := by
      rw [inv_pow, Real.sq_sqrt (by positivity), mul_inv_cancel₀ (by positivity)]

private lemma pf_precision (m : ℕ) (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    8 / Real.pi ^ 2 ≤ probEvent (aeVartheta m (Real.pi * ω))
      (fun a => circDist ((bitsToNat a : ℝ) / (2 : ℝ) ^ m) ω ≤ 1 / (2 : ℝ) ^ m) := by
  classical
  by_cases hm : 2 ≤ m
  · have hM : 2 < 2 ^ m := by
      calc
        2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    have h := QAmpEst.Est.theorem_11_eight_over_pi_sq (2 ^ m) hM ω hω0 hω1
    simp only [Finset.sum_filter, pf_distance, Nat.cast_pow, Nat.cast_ofNat] at h
    rw [← (bitsEquivFin m).sum_comp] at h
    simpa only [bitsEquivFin_apply, pf_prob, probEvent, Finset.sum_filter] using h
  · have hN : (2 : ℝ) ^ m ≤ 2 := by
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;> norm_num
    have he (a : Qubits m) : circDist ((bitsToNat a : ℝ) / (2 : ℝ) ^ m) ω ≤ 1 / (2 : ℝ) ^ m := by
      apply (abs_sub_round _).trans
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ m)).2
      linarith
    have hp : 8 / Real.pi ^ 2 ≤ 1 := by
      apply (div_le_one (by positivity : 0 < Real.pi ^ 2)).2
      nlinarith [Real.pi_gt_three]
    simpa only [probEvent, Finset.filter_true_of_mem (fun a _ => he a), pf_total] using hp

private lemma pf_sin_sq_period (x : ℝ) (k : ℤ) :
    Real.sin (x - (k : ℝ) * Real.pi) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_sub_int_mul_pi, mul_pow]
  have hk : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul]
    norm_num
  rw [hk, one_mul]

private lemma pf_circle_error (m : ℕ) (ω : ℝ) (a : Qubits m)
    (h : circDist ((bitsToNat a : ℝ) / (2 : ℝ) ^ m) ω ≤ 1 / (2 : ℝ) ^ m) :
    |Real.sin (Real.pi * ω) ^ 2 - Real.sin (aeAngle a) ^ 2| ≤
      2 * Real.pi * Real.sqrt (Real.sin (Real.pi * ω) ^ 2 *
        (1 - Real.sin (Real.pi * ω) ^ 2)) / (2 : ℝ) ^ m +
        Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) := by
  let x := (bitsToNat a : ℝ) / (2 : ℝ) ^ m
  let k := round (x - ω)
  let d := Real.pi * ((x - ω) - (k : ℝ))
  have hd : |d| ≤ Real.pi / (2 : ℝ) ^ m := by
    dsimp [d,k,x]
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left h Real.pi_pos.le).trans_eq (by ring)
  have hs : Real.sin (Real.pi * ω + d) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
    rw [show Real.pi * ω + d = Real.pi * x - (k : ℝ) * Real.pi by dsimp [d]; ring]
    exact pf_sin_sq_period _ _
  have ha : Real.sin (aeAngle a) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
    unfold aeAngle
    split_ifs
    · rw [show Real.pi * (1 - (bitsToNat a : ℝ) * ((2 : ℝ) ^ m)⁻¹) =
        Real.pi - Real.pi * x by dsimp [x]; ring, Real.sin_pi_sub]
    · rfl
  have hr : Real.sqrt (Real.sin (Real.pi * ω) ^ 2 * (1 - Real.sin (Real.pi * ω) ^ 2)) =
      |Real.sin (Real.pi * ω) * Real.cos (Real.pi * ω)| := by
    rw [show 1 - Real.sin (Real.pi * ω) ^ 2 = Real.cos (Real.pi * ω) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * ω)], ← mul_pow, Real.sqrt_sq_eq_abs]
  have hb := sin_sq_error (Real.pi * ω) d
  rw [hs] at hb
  rw [ha, abs_sub_comm, hr]
  apply hb.trans
  have hsq : |d| ^ 2 ≤ (Real.pi / (2 : ℝ) ^ m) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hmul := mul_le_mul_of_nonneg_right hd
    (abs_nonneg (Real.sin (Real.pi * ω) * Real.cos (Real.pi * ω)))
  rw [show (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 by rw [mul_comm 2 m, pow_mul]]
  calc
    _ ≤ 2 * (Real.pi / (2 : ℝ) ^ m) * |Real.sin (Real.pi * ω) * Real.cos (Real.pi * ω)| +
        (Real.pi / (2 : ℝ) ^ m) ^ 2 := add_le_add (by nlinarith [hmul]) hsq
    _ = _ := by ring

private lemma pf_act_linear {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) (c d : ℂ) :
    act A (c • u + d • v) = c • act A u + d • act A v := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_add_distrib,
    mul_add, mul_assoc, mul_left_comm]

private lemma pf_slice_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) (c d : ℂ) (a : Qubits m) :
    (WithLp.toLp 2 (fun b => phaseEstimationState m U (c • u + d • v) (a,b)) : EuclideanSpace ℂ ι) =
      c • WithLp.toLp 2 (fun b => phaseEstimationState m U u (a,b)) +
        d • WithLp.toLp 2 (fun b => phaseEstimationState m U v (a,b)) := by
  have ht : tensorVec (zeroKet m) (c • u + d • v) =
      c • tensorVec (zeroKet m) u + d • tensorVec (zeroKet m) v := by
    ext z
    simp [tensorVec]
    ring
  ext b
  simp only [phaseEstimationState, ht, pf_act_linear, PiLp.toLp_apply, PiLp.add_apply,
    PiLp.smul_apply]

private lemma pf_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) (c d : ℂ) (ω σ : ℝ)
    (hu : IsState u) (hv : IsState v) (huv : inner ℂ u v = 0)
    (heu : act U u = Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ)) • u)
    (hev : act U v = Complex.exp (2 * Real.pi * Complex.I * (σ : ℂ)) • v)
    (P : Qubits m → Prop) [DecidablePred P] :
    probEvent (phaseEstimationState m U (c • u + d • v)) (fun z => P z.1) =
      ‖c‖ ^ 2 * probEvent (aeVartheta m (Real.pi * ω)) P +
        ‖d‖ ^ 2 * probEvent (aeVartheta m (Real.pi * σ)) P := by
  classical
  change ‖u‖ = 1 at hu
  change ‖v‖ = 1 at hv
  have hp (a : Qubits m) :
      ‖(WithLp.toLp 2 (fun b => phaseEstimationState m U (c • u + d • v) (a,b)) : EuclideanSpace ℂ ι)‖ ^ 2 =
        ‖c‖ ^ 2 * prob (aeVartheta m (Real.pi * ω)) a +
          ‖d‖ ^ 2 * prob (aeVartheta m (Real.pi * σ)) a := by
    rw [pf_slice_linear, pf_eigen_slice _ _ _ _ heu, pf_eigen_slice _ _ _ _ hev]
    have hi : inner ℂ (c • (aeVartheta m (Real.pi * ω) a • u))
        (d • (aeVartheta m (Real.pi * σ) a • v)) = 0 := by
      simp [huv]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
    simpa only [norm_smul, hu, hv, mul_one, prob, ket, EuclideanSpace.inner_single_left,
      map_one, one_mul, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  rw [ip_event_slices]
  simp only [hp, probEvent, Finset.sum_add_distrib, Finset.mul_sum]

private lemma pf_success (m : ℕ) (ω θ : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hs : Real.sin (Real.pi * ω) ^ 2 = Real.sin θ ^ 2) :
    8 / Real.pi ^ 2 ≤ probEvent (aeVartheta m (Real.pi * ω))
      (fun a => |Real.sin θ ^ 2 - Real.sin (aeAngle a) ^ 2| ≤
        2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) / (2 : ℝ) ^ m +
          Real.pi ^ 2 / (2 : ℝ) ^ (2 * m)) := by
  classical
  apply (pf_precision m ω hω0 hω1).trans
  unfold probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simpa only [hs] using pf_circle_error m ω a ha
  · intro a _ _
    exact sq_nonneg _

theorem solution {n : ℕ} (m : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) fun z =>
      |Real.sin θ ^ 2 - Real.sin (aeAngle z.1) ^ 2| ≤
        2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) / (2 : ℝ) ^ m +
          Real.pi ^ 2 / (2 : ℝ) ^ (2 * m) := by
  classical
  let u := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG + Complex.I • psiB)
  let v := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG - Complex.I • psiB)
  let c : ℂ := ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sin θ : ℂ) - Complex.I * (Real.cos θ : ℂ))
  let d : ℂ := ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sin θ : ℂ) + Complex.I * (Real.cos θ : ℂ))
  let ω := θ / Real.pi
  let σ := if θ = 0 then 0 else 1 - ω
  have he := QAlgorithms.Nannicini.groverOperator_eigenstates S R psiG psiB θ
    hS hR hG hB horth hθ0 hθ1 hprep hRG hRB
  change IsState u ∧ IsState v ∧ inner ℂ u v = 0 ∧ _ ∧ _ at he
  obtain ⟨hu,hv,huv,heu,hev⟩ := he
  have hω0 : 0 ≤ ω := div_nonneg hθ0 Real.pi_pos.le
  have hωhalf : ω ≤ 1 / 2 := (div_le_iff₀ Real.pi_pos).2 (by linarith)
  have hω1 : ω < 1 := by linarith
  have hσ0 : 0 ≤ σ := by dsimp [σ]; split_ifs <;> linarith
  have hσ1 : σ < 1 := by
    dsimp [σ]
    split_ifs with hz
    · norm_num
    · have hθ : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
      have hp : 0 < ω := div_pos hθ Real.pi_pos
      linarith
  have hπω : Real.pi * ω = θ := by dsimp [ω]; field_simp
  have hsinσ : Real.sin (Real.pi * σ) ^ 2 = Real.sin θ ^ 2 := by
    dsimp [σ]
    split_ifs with hz
    · simp [hz]
    · rw [mul_sub, mul_one, hπω, Real.sin_pi_sub]
  have heω : act (ampAmpIterate S R 0) u =
      Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ)) • u := by
    rw [heu]
    congr 2
    have hh := congrArg (fun x : ℝ => (x : ℂ)) hπω
    push_cast at hh
    linear_combination -2 * Complex.I * hh
  have heσ : act (ampAmpIterate S R 0) v =
      Complex.exp (2 * Real.pi * Complex.I * (σ : ℂ)) • v := by
    rw [hev]
    congr 1
    dsimp [σ]
    split_ifs with hz
    · simp [hz]
    · have harg : 2 * (Real.pi : ℂ) * Complex.I * ((1 - ω : ℝ) : ℂ) =
          2 * (Real.pi : ℂ) * Complex.I + -(2 * Complex.I * (θ : ℂ)) := by
        have hh := congrArg (fun x : ℝ => (x : ℂ)) hπω
        push_cast at hh ⊢
        linear_combination -2 * Complex.I * hh
      rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  have hroot : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hscale : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) * 2 = 1 := by
    field_simp [hr0]
    exact hroot.symm
  have hdec : act S (zeroKet n) = c • u + d • v := by
    rw [hprep]
    symm
    ext j
    simp only [c,d,u,v,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    linear_combination ((Real.sin θ : ℂ) * psiG j + (Real.cos θ : ℂ) * psiB j) * hscale -
      2 * ((Real.sqrt 2)⁻¹ : ℂ)^2 * (Real.cos θ : ℂ) * psiB j * Complex.I_sq
  have hnorm (sgn : ℂ) (hsgn : sgn = 1 ∨ sgn = -1) :
      ‖((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sin θ : ℂ) + sgn * Complex.I * (Real.cos θ : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
    rcases hsgn with rfl | rfl <;>
      simp [Complex.normSq_apply, Real.sin_sq_add_cos_sq, inv_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    all_goals
      rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
      simp only [Complex.ofReal_re]
      nlinarith [Real.sin_sq_add_cos_sq θ]
  have hc : ‖c‖ ^ 2 = 1 / 2 := by
    simpa only [c, neg_mul, one_mul, add_neg_cancel_right, sub_eq_add_neg] using
      hnorm (-1) (Or.inr rfl)
  have hd : ‖d‖ ^ 2 = 1 / 2 := by simpa only [d,one_mul] using hnorm 1 (Or.inl rfl)
  let P := fun a : Qubits m => |Real.sin θ ^ 2 - Real.sin (aeAngle a) ^ 2| ≤
        2 * Real.pi * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) / (2 : ℝ) ^ m +
          Real.pi ^ 2 / (2 : ℝ) ^ (2 * m)
  have hp := pf_success m ω θ hω0 hω1 (by rw [hπω])
  have hq := pf_success m σ θ hσ0 hσ1 hsinσ
  change 8 / Real.pi ^ 2 ≤ probEvent (aeState m S R) (fun z => P z.1)
  rw [aeState,hdec,pf_mixture m _ u v c d ω σ hu hv huv heω heσ P,hc,hd]
  linarith
