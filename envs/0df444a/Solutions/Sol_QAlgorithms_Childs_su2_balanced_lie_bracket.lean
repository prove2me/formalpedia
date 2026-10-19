-- Prove2me | solution 1 for QAlgorithms.Childs.su2_balanced_lie_bracket
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:19:02.044525+00:00
-- url     : https://prove2.me/submissions/bceb5fd1-5cf8-4b3a-995d-6fc41a37d8f5

import Definitions.Def_QAlgorithms_Defs_Circuit
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FinCases

open QAlgorithms NormedSpace
open scoped Matrix.Norms.L2Operator

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private lemma exp_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ) (Z : Mat) :
    exp (Unitary.conjStarAlgAut ℂ Mat U Z) =
      Unitary.conjStarAlgAut ℂ Mat U (exp Z) := by
  let : NormedAlgebra ℚ Mat := NormedAlgebra.restrictScalars ℚ ℂ Mat
  exact (map_exp (Unitary.conjStarAlgAut ℂ Mat U)
    (by
      change Continuous (fun Z : Mat => (U : Mat) * Z * star (U : Mat))
      fun_prop) Z).symm

private lemma det_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ) (Z : Mat) :
    (Unitary.conjStarAlgAut ℂ Mat U Z).det = Z.det := by
  simp only [Unitary.conjStarAlgAut_apply, Matrix.det_mul]
  have h := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul, Matrix.det_one, Unitary.coe_star] at h

  calc
    _ = ((U : Mat).det * (star (U : Mat)).det) * Z.det := by ring
    _ = _ := by rw [h, one_mul]

private lemma norm_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ) (Z : Mat) :
    ‖Unitary.conjStarAlgAut ℂ Mat U Z‖ = ‖Z‖ := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.property),
    CStarRing.norm_mem_unitary_mul _ U.property]

private lemma det_exp_skew (H : Mat) (hH : H.IsHermitian) :
    (exp (Complex.I • H)).det = Complex.exp (Complex.I * H.trace) := by
  let U := hH.eigenvectorUnitary
  let d : Fin 2 → ℂ := fun j => (hH.eigenvalues j : ℂ)
  have hdiag : H = Unitary.conjStarAlgAut ℂ Mat U (Matrix.diagonal d) := hH.spectral_theorem
  have ht : H.trace = d 0 + d 1 := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp [d, Fin.sum_univ_two]
  calc
    _ = (exp (Complex.I • Unitary.conjStarAlgAut ℂ Mat U (Matrix.diagonal d))).det := by rw [← hdiag]
    _ = (exp (Complex.I • Matrix.diagonal d)).det := by rw [← map_smul, exp_conjugate, det_conjugate]
    _ = Complex.exp (Complex.I * H.trace) := by
      rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.det_diagonal, ht]
      simp only [Fin.prod_univ_two, Pi.smul_apply, smul_eq_mul, Pi.coe_exp,
        ← Complex.exp_eq_exp_ℂ, mul_add, Complex.exp_add]

private lemma exp_skew_special (H : Mat) (hH : H.IsHermitian) (ht : H.trace = 0) :
    exp (Complex.I • H) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · exact (selfAdjoint.expUnitary ⟨H, hH⟩).property
  · rw [det_exp_skew H hH, ht, mul_zero, Complex.exp_zero]

private def px : Mat := !![0, 1; -1, 0]
private def py : Mat := !![0, Complex.I; Complex.I, 0]

private lemma px_star : star px = -px := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [px]
private lemma py_star : star py = -py := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [py]
private lemma px_unitary : px ∈ unitary Mat := by
  rw [Unitary.mem_iff]
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [px, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two])
private lemma py_unitary : py ∈ unitary Mat := by
  rw [Unitary.mem_iff]
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [py, Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two])

private lemma skew_exp_special (Z : Mat) (hz : star Z = -Z) (ht : Z.trace = 0) :
    exp Z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hH : IsSelfAdjoint ((-Complex.I) • Z) := by
    simp only [isSelfAdjoint_iff, star_smul, hz]
    simp [smul_neg, neg_smul]
  have hid : Complex.I • ((-Complex.I) • Z) = Z := by
    rw [smul_smul]; simp
  rw [← hid]
  apply exp_skew_special _ hH
  simp [Matrix.trace_smul, ht]

private lemma balanced_skew (H : Mat) (hH : H.IsHermitian) (ht : H.trace = 0) :
    ∃ X Y : Mat, ‖X‖ ≤ Real.sqrt (‖H‖ / 2) ∧ ‖Y‖ ≤ Real.sqrt (‖H‖ / 2) ∧
      exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      exp Y ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧ X * Y - Y * X = Complex.I • H := by
  let U := hH.eigenvectorUnitary
  let a := hH.eigenvalues 0
  have hneg : hH.eigenvalues 1 = -a := by
    have he := hH.trace_eq_sum_eigenvalues
    rw [ht] at he
    simp only [Fin.sum_univ_two] at he
    have hr := congrArg RCLike.re he
    simp only [map_add, RCLike.ofReal_re, RCLike.zero_re] at hr
    dsimp [a]; linarith
  let t := Real.sqrt (|a| / 2)
  let b := if 0 ≤ a then t else -t
  have htpos : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = |a| / 2 := Real.sq_sqrt (by positivity)
  have hbt : |b| = t := by dsimp [b]; split_ifs <;> simp [abs_of_nonneg htpos]
  have hprod : 2 * t * b = a := by
    dsimp [b]; split_ifs with ha
    · rw [abs_of_nonneg ha] at htsq; nlinarith
    · rw [abs_of_neg (lt_of_not_ge ha)] at htsq; nlinarith
  let X₀ : Mat := (t : ℂ) • px
  let Y₀ : Mat := (b : ℂ) • py
  let F := Unitary.conjStarAlgAut ℂ Mat U
  have hx : exp X₀ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    apply skew_exp_special
    · dsimp [X₀]; rw [star_smul, px_star]; simp
    · simp [X₀, Matrix.trace, px, Fin.sum_univ_two]
  have hy : exp Y₀ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    apply skew_exp_special
    · dsimp [Y₀]; rw [star_smul, py_star]; simp
    · simp [Y₀, Matrix.trace, py, Fin.sum_univ_two]
  have haH : |a| ≤ ‖H‖ := by
    simpa [a, Real.norm_eq_abs] using
      (spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real 0))
  have hnorm : t ≤ Real.sqrt (‖H‖ / 2) := Real.sqrt_le_sqrt (by linarith)
  have ha : hH.eigenvalues 0 = a := rfl
  have hc : X₀ * Y₀ - Y₀ * X₀ =
      Complex.I • Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [X₀, Y₀, px, py, hneg, ha]
    all_goals
      have hp : (2 : ℂ) * (t : ℂ) * (b : ℂ) = (a : ℂ) := by exact_mod_cast hprod
      first
      | solve | linear_combination (norm := ring_nf) Complex.I * hp
      | solve | linear_combination (norm := ring_nf) -Complex.I * hp
  refine ⟨F X₀, F Y₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_conjugate, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg htpos, CStarRing.norm_coe_unitary ⟨px, px_unitary⟩, mul_one]
    exact hnorm
  · rw [norm_conjugate, norm_smul, Complex.norm_real, Real.norm_eq_abs, hbt,
      CStarRing.norm_coe_unitary ⟨py, py_unitary⟩, mul_one]
    exact hnorm
  · rw [exp_conjugate, Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨Unitary.map_mem F hx.1, by
      rw [det_conjugate]; exact hx.2⟩
  · rw [exp_conjugate, Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨Unitary.map_mem F hy.1, by
      rw [det_conjugate]; exact hy.2⟩
  · rw [← map_mul, ← map_mul, ← map_sub, hc, map_smul]
    congr 1
    exact hH.spectral_theorem.symm

private lemma log_small_radius :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ U : unitary Mat,
      ‖(U : Mat) - 1‖ ≤ δ → ‖Unitary.argSelfAdjoint U‖ ≤ (1 / 9 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ => Real.arccos (1 - x ^ 2 / 2)) 0 := by fun_prop
  obtain ⟨d, hd, hbound⟩ := Metric.continuousAt_iff.mp hc (1 / 9) (by norm_num)
  refine ⟨min (d / 2) 1, lt_min (by positivity) zero_lt_one, min_le_right _ _, ?_⟩
  intro U hu
  have h1 : ‖(U : Mat) - 1‖ < 2 := lt_of_le_of_lt (hu.trans (min_le_right _ _)) (by norm_num)
  rw [Unitary.norm_argSelfAdjoint h1]
  have he := hbound (x := ‖(U : Mat) - 1‖) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact lt_of_le_of_lt (hu.trans (min_le_left _ _)) (by linarith))
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, Real.arccos_one,
    Real.dist_eq] at he
  exact (le_abs_self _).trans he.le

private lemma exp_remainder (X : Mat) (hX : ‖X‖ ≤ 1) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 := by
  have hs := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) X)
  have ht := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    pow_zero, pow_one, one_smul] at hs ht
  have hb : ‖exp X - (1 + X)‖ ≤ exp ‖X‖ - (1 + ‖X‖) := by
    apply hs.norm_le_of_bounded ht
    intro n
    simp only [norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le X (n + 2)) (by positivity)
  have hr := Real.norm_exp_sub_one_sub_id_le (x := ‖X‖) (by simpa using hX)
  rw [Real.exp_eq_exp_ℝ] at hr
  calc
    _ = ‖exp X - (1 + X)‖ := by congr 1; abel
    _ ≤ exp ‖X‖ - (1 + ‖X‖) := hb
    _ ≤ ‖exp ‖X‖ - 1 - ‖X‖‖ := by
      simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using
        (le_abs_self (exp ‖X‖ - 1 - ‖X‖))
    _ ≤ ‖X‖ ^ 2 := by simpa using hr

private lemma log_bound (U : unitary Mat) (hu : ‖(U : Mat) - 1‖ < 2)
    (hsmall : ‖Unitary.argSelfAdjoint U‖ ≤ (1 / 9 : ℝ)) :
    ‖Unitary.argSelfAdjoint U‖ ≤ (9 / 8 : ℝ) * ‖(U : Mat) - 1‖ := by
  let H := Unitary.argSelfAdjoint U
  let X : Mat := Complex.I • (H : Mat)
  have hn : ‖X‖ = ‖H‖ := by simp [X, norm_smul]
  have he : exp X = (U : Mat) := congrArg Subtype.val (expUnitary_argSelfAdjoint hu)
  have hr := exp_remainder X (by rw [hn]; exact hsmall.trans (by norm_num))
  rw [hn, he] at hr
  have hi0 : ‖X‖ - ‖(U : Mat) - 1‖ ≤ ‖(U : Mat) - 1 - X‖ := by
    simpa only [norm_sub_rev] using (norm_sub_norm_le X ((U : Mat) - 1))
  rw [hn] at hi0
  have hi : ‖H‖ ≤ ‖(U : Mat) - 1‖ + ‖H‖ ^ 2 := by linarith only [hi0, hr]

  have hq : ‖H‖ ^ 2 ≤ ‖H‖ / 9 := by nlinarith [norm_nonneg H]
  change ‖H‖ ≤ _
  linarith

private lemma log_traceless (A : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hu : ‖(A : Mat) - 1‖ < 2)
    (hsmall : ‖Unitary.argSelfAdjoint (⟨(A : Mat), A.property.1⟩ : unitary Mat)‖ ≤ (1 / 9 : ℝ)) :
    (Unitary.argSelfAdjoint (⟨(A : Mat), A.property.1⟩ : unitary Mat) : Mat).trace = 0 := by
  let U : unitary Mat := ⟨(A : Mat), A.property.1⟩
  let H := Unitary.argSelfAdjoint U
  have hH : (H : Mat).IsHermitian := H.property
  let s : ℝ := hH.eigenvalues 0 + hH.eigenvalues 1
  have ht : (H : Mat).trace = (s : ℂ) := by
    rw [hH.trace_eq_sum_eigenvalues]; simp [s, Fin.sum_univ_two]
  have hb (j : Fin 2) : |hH.eigenvalues j| ≤ (1 / 9 : ℝ) := by
    exact (spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real j)).trans hsmall
  have hs : |s| ≤ (2 / 9 : ℝ) := by
    exact (abs_add_le _ _).trans (by linarith [hb 0, hb 1])
  have he : Complex.exp (Complex.I * (s : ℂ)) = 1 := by
    rw [← ht, ← det_exp_skew _ hH]
    have he := congrArg Subtype.val (expUnitary_argSelfAdjoint (u := U) hu)
    change exp (Complex.I • (H : Mat)) = (A : Mat) at he
    rw [he]; exact A.property.2
  have hz := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := Complex.I * (s : ℂ)) (y := 0)
    (by simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]; linarith [abs_le.mp hs, Real.pi_gt_three])
    (by simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]; linarith [abs_le.mp hs, Real.pi_gt_three])
    (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)
    (by simpa using he)
  rw [ht]
  simpa using congrArg Complex.im hz

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ A ∈ QAlgorithms.su2Ball (ε ^ 2),
        ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ,
          QAlgorithms.specNorm X ≤ (3 / 4 : ℝ) * ε ∧
          QAlgorithms.specNorm Y ≤ (3 / 4 : ℝ) * ε ∧
          NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
          NormedSpace.exp Y ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
          (A : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (X * Y - Y * X) := by
  obtain ⟨δ, hd, hd1, hsmall⟩ := log_small_radius
  refine ⟨δ, hd, ?_⟩
  intro ε he heδ A hA
  let U : unitary Mat := ⟨(A : Mat), A.property.1⟩
  let H := Unitary.argSelfAdjoint U
  have hε1 : ε ≤ 1 := heδ.trans hd1
  have hdist : ‖(U : Mat) - 1‖ ≤ ε ^ 2 := by
    change ‖(A : Mat) - 1‖ ≤ ε ^ 2
    change ‖1 - (A : Mat)‖ ≤ ε ^ 2 at hA
    rwa [norm_sub_rev]
  have hδ : ‖(U : Mat) - 1‖ ≤ δ := hdist.trans (by nlinarith)
  have hu : ‖(U : Mat) - 1‖ < 2 := lt_of_le_of_lt (hδ.trans hd1) (by norm_num)
  have hHsmall : ‖H‖ ≤ (1 / 9 : ℝ) := hsmall U hδ
  have hHbound : ‖H‖ ≤ (9 / 8 : ℝ) * ε ^ 2 :=
    (log_bound U hu hHsmall).trans (mul_le_mul_of_nonneg_left hdist (by norm_num))
  have ht : (H : Mat).trace = 0 := log_traceless A hu hHsmall
  obtain ⟨X, Y, hx, hy, hxu, hyu, hbr⟩ := balanced_skew (H : Mat) H.property ht
  have hb : Real.sqrt (‖(H : Mat)‖ / 2) ≤ (3 / 4 : ℝ) * ε := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by change ‖H‖ / 2 ≤ _; nlinarith⟩
  refine ⟨X, Y, hx.trans hb, hy.trans hb, hxu, hyu, ?_⟩
  rw [hbr]
  exact (congrArg Subtype.val (expUnitary_argSelfAdjoint (u := U) hu)).symm
