-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.epsilon_region_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:37:38.367283+00:00
-- url     : https://prove2.me/submissions/5a8dccc7-0f11-4d21-b82a-66623525ef98

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section
open QAlgorithms.Papers.Independent.Next46.P21
open Set
open scoped ComplexConjugate Matrix

def g64a_qm (a b : ℂ) : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then star a else b) else (if j then -star b else a)

theorem g64a_qm_norm (a b : ℂ) :
    QAlgorithms.specNorm (g64a_qm a b) ^ 2 = Complex.normSq a + Complex.normSq b := by
  have hM : (g64a_qm a b)ᴴ * g64a_qm a b =
      Matrix.diagonal (fun _ => ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ)) := by
    ext i j
    cases i <;> cases j <;>
      simp [g64a_qm, Matrix.mul_apply, Fintype.univ_bool, Complex.normSq_eq_conj_mul_self] <;> ring
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (g64a_qm a b)
  unfold QAlgorithms.specNorm
  rw [sq, ← h, hM, Matrix.l2_opNorm_diagonal]
  have hc : 0 ≤ Complex.normSq a + Complex.normSq b := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rw [pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem g64a_det (A : Matrix Bool Bool ℂ) :
    A.det = A false false * A true true - A false true * A true false := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm A, Matrix.det_fin_two]
  simp [finTwoEquiv]

theorem g64a_zphase_conj (theta : ℝ) :
    Complex.exp (Complex.I * (theta : ℂ) / 2) = star (zPhase theta) := by
  rw [zPhase, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_div₀, map_ofNat]

theorem g64a_zphase_normSq (theta : ℝ) : Complex.normSq (zPhase theta) = 1 := by
  rw [Complex.normSq_eq_norm_sq, zPhase, Complex.norm_exp]
  simp

theorem g64a_qm_su (a b : ℂ) (h : star a * a + star b * b = 1) :
    g64a_qm a b ∈ Matrix.specialUnitaryGroup Bool ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  simp only [Complex.star_def] at h
  have h' : (Complex.normSq a : ℂ) + Complex.normSq b = 1 := by
    rw [← Complex.mul_conj, ← Complex.mul_conj]; linear_combination h
  constructor
  · ext i j
    cases i <;> cases j <;>
      simp [g64a_qm, Matrix.mul_apply, Fintype.univ_bool, Matrix.star_apply, Complex.mul_conj] <;>
      (try rw [← Complex.normSq_eq_conj_mul_self]) <;>
      first | exact h' | (rw [add_comm]; exact h') | ring | linear_combination h' | (rw [mul_comm a, mul_comm b, Complex.mul_conj, Complex.mul_conj]; linear_combination h') | (rw [mul_comm a, Complex.mul_conj]; linear_combination h') | (rw [mul_comm b, Complex.mul_conj]; linear_combination h')
  · rw [g64a_det]
    simp [g64a_qm]
    linear_combination h

theorem g64a_main (eps theta : ℝ) (k : ℕ) (u t : ℂ)
    (heps : 0 < eps)
    (hnorm : star u * u + star t * t = (2 : ℂ) ^ k) :
    completion k u t ∈ Matrix.specialUnitaryGroup Bool ℂ ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      Complex.normSq (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ) - zPhase theta) +
        Complex.normSq (t / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      2 - 2 * (star (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) * zPhase theta).re ∧
    (QAlgorithms.specNorm (completion k u t - zRotation theta) ≤ eps ↔
      (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta) := by
  set D : ℂ := (Real.sqrt ((2 : ℝ) ^ k) : ℂ) with hD
  set u' := u / D with hu'
  set t' := t / D with ht'
  set z := zPhase theta with hz
  have hD2 : Complex.normSq D = 2 ^ k := by
    rw [hD, Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]
  have hDpos : 0 < Complex.normSq D := by rw [hD2]; positivity
  have hreal : Complex.normSq u + Complex.normSq t = 2 ^ k := by
    have : ((Complex.normSq u + Complex.normSq t : ℝ) : ℂ) = ((2 ^ k : ℝ) : ℂ) := by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using hnorm
    exact_mod_cast this
  have h1 : Complex.normSq u' + Complex.normSq t' = 1 := by
    rw [hu', ht', Complex.normSq_div, Complex.normSq_div, hD2, ← add_div, hreal]
    exact div_self (by positivity)
  have h1c : star u' * u' + star t' * t' = 1 := by
    have : ((Complex.normSq u' + Complex.normSq t' : ℝ) : ℂ) = 1 := by rw [h1]; simp
    push_cast at this
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at this
    simpa [Complex.star_def] using this
  have hC : completion k u t = g64a_qm u' t' := rfl
  have hM : completion k u t - zRotation theta = g64a_qm (u' - z) t' := by
    rw [hC]
    ext i j
    cases i <;> cases j <;> simp [g64a_qm, zRotation, g64a_zphase_conj, hz]
  have hzn := g64a_zphase_normSq theta
  rw [← hz] at hzn
  have hre : (star u' * z).re = (u' * star z).re := by
    rw [← Complex.conj_re (star u' * z)]
    simp [Complex.star_def, mul_comm]
  have e2 : QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      Complex.normSq (u' - z) + Complex.normSq t' := by rw [hM, g64a_qm_norm]
  have e3 : QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      2 - 2 * (star u' * z).re := by
    rw [e2, Complex.normSq_sub, hre, hzn, ← Complex.star_def]
    linarith
  refine ⟨?_, e2, e3, ?_⟩
  · rw [hC]; exact g64a_qm_su _ _ h1c
  · have hs0 : 0 ≤ QAlgorithms.specNorm (completion k u t - zRotation theta) := by
      unfold QAlgorithms.specNorm; exact @norm_nonneg _ (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℂ) (m := Bool) (n := Bool)).toSeminormedAddCommGroup.toSeminormedAddGroup _
    simp only [epsilonRegion, unitDisk, Set.mem_ofPred_eq]
    have hu1 : Complex.normSq u' ≤ 1 := by linarith [Complex.normSq_nonneg t']
    constructor
    · intro h
      refine ⟨hu1, ?_⟩
      have : QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 ≤ eps ^ 2 :=
        pow_le_pow_left₀ hs0 h 2
      linarith
    · rintro ⟨-, h⟩
      have : QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 ≤ eps ^ 2 := by
        linarith
      exact (pow_le_pow_iff_left₀ hs0 heps.le (by norm_num)).1 this

theorem solution (eps theta : ℝ) (k : ℕ) (u t : ℂ)
    (heps : 0 < eps) (hu : IsCyclotomicInteger u) (ht : IsCyclotomicInteger t)
    (hnorm : star u * u + star t * t = (2 : ℂ) ^ k) :
    completion k u t ∈ Matrix.specialUnitaryGroup Bool ℂ ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      Complex.normSq (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ) - zPhase theta) +
        Complex.normSq (t / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∧
    QAlgorithms.specNorm (completion k u t - zRotation theta) ^ 2 =
      2 - 2 * (star (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) * zPhase theta).re ∧
    (QAlgorithms.specNorm (completion k u t - zRotation theta) ≤ eps ↔
      (u / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta) :=
  g64a_main eps theta k u t heps hnorm
