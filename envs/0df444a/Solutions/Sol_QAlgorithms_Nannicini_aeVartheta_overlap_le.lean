-- Prove2me | solution 1 for QAlgorithms.Nannicini.aeVartheta_overlap_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:44:24.757565+00:00
-- url     : https://prove2.me/submissions/4d529793-dcc3-4a07-91f2-92f99b756c35

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation

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

private lemma vo_overlap (m : ℕ) (θ : ℝ) :
    inner ℂ (aeVartheta m (-θ)) (aeVartheta m θ) =
      (∑ k ∈ Finset.range (2 ^ m), Complex.exp (4 * Complex.I * (θ : ℂ)) ^ k) /
        (2 : ℂ) ^ m := by
  unfold aeVartheta
  rw [vo_inner _ (Unitary.star_mem (vo_qubits_unitary m))]
  have hs : (Real.sqrt ((2 : ℝ) ^ m) : ℂ) ^ 2 = (2 : ℂ) ^ m := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : Qubits m,
    (Complex.exp (2 * Complex.I * (θ : ℂ) * (bitsToNat k : ℂ)) *
      ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ)) *
    star (Complex.exp (2 * Complex.I * ((-θ : ℝ) : ℂ) * (bitsToNat k : ℂ)) *
      ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ))) = _
  simp only [Complex.star_def, map_mul, map_inv₀, ← Complex.exp_conj,
    map_ofNat, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg,
    Complex.conj_natCast]
  have he (k : Qubits m) :
      (2 * -Complex.I * -(θ : ℂ) * (bitsToNat k : ℂ)) +
        (2 * Complex.I * (θ : ℂ) * (bitsToNat k : ℂ)) =
      (bitsToNat k : ℂ) * (4 * Complex.I * (θ : ℂ)) := by ring
  have ht (k : Qubits m) :
      (Complex.exp (2 * Complex.I * (θ : ℂ) * (bitsToNat k : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ)) *
      (Complex.exp (2 * -Complex.I * -(θ : ℂ) * (bitsToNat k : ℂ)) *
        ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ)) =
      Complex.exp (4 * Complex.I * (θ : ℂ)) ^ bitsToNat k / (2 : ℂ) ^ m := by
    rw [show ∀ a b c : ℂ, a * b * (c * b) = (c * a) * b ^ 2 by intros; ring]
    rw [← Complex.exp_add, he, Complex.exp_nat_mul]
    push_cast
    rw [inv_pow, hs]
    rfl
  simp_rw [ht]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [← bitsEquivFin_apply]
  rw [(bitsEquivFin m).sum_comp (fun k : Fin (2 ^ m) =>
    Complex.exp (4 * Complex.I * (θ : ℂ)) ^ (k : ℕ)), Fin.sum_univ_eq_sum_range]

theorem solution (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ‖inner ℂ (aeVartheta m (-θ)) (aeVartheta m θ)‖ ≤
      1 / ((2 : ℝ) ^ m * Real.sin (2 * θ)) := by
  have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  let r : ℂ := Complex.exp (4 * Complex.I * (θ : ℂ))
  have hr : ‖r‖ = 1 := by
    dsimp [r]
    rw [show 4 * Complex.I * (θ : ℂ) = ((4 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (4 * θ)
  have hd : ‖r - 1‖ = 2 * Real.sin (2 * θ) := by
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (4 * θ)
    have he : Complex.I * ((4 * θ : ℝ) : ℂ) = 4 * Complex.I * (θ : ℂ) := by push_cast; ring
    rw [he, show (4 * θ) / 2 = 2 * θ by ring, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hs)] at h
    exact h
  have hg := congrArg norm (geom_sum_mul r (2 ^ m))
  rw [norm_mul, hd] at hg
  have hu : ‖r ^ (2 ^ m) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖r ^ (2 ^ m)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hr]; norm_num
  have hb : ‖∑ k ∈ Finset.range (2 ^ m), r ^ k‖ ≤ 1 / Real.sin (2 * θ) := by
    apply (le_div_iff₀ hs).2
    nlinarith [hg]
  rw [vo_overlap, norm_div]
  have hn : ‖(2 : ℂ) ^ m‖ = (2 : ℝ) ^ m := by simp [norm_pow]
  rw [hn]
  calc
    _ ≤ (1 / Real.sin (2 * θ)) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by ring
