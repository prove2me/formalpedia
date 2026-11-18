-- Prove2me | solution 1 for QSampVerif.lemma_13_11
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T14:55:27.865328+00:00
-- url     : https://prove2.me/submissions/ff3d2a8e-b1af-477c-ba6d-c0160c5684af

import Definitions.Def_QSampVerif_zPhase
import Definitions.Def_QSampVerif_refMass


set_option autoImplicit false

namespace QSampVerif

lemma norm_zPhase (k : Fin 4) : ‖zPhase k‖ = 1 := by
  simp [zPhase, norm_pow]

lemma scalar_polarization (a b c d : ℂ) :
    a * star d = ∑ k : Fin 4, zPhase k *
      ((2⁻¹ : ℂ) * (a + zPhase k * b) *
        star ((2⁻¹ : ℂ) * (c + zPhase k * d))) := by
  simp [Fin.sum_univ_four, zPhase, pow_succ, Complex.I_sq, map_add, map_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem vector_polarization {ι : Type*} [Fintype ι]
    (a b : EuclideanSpace ℂ ι) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    Matrix.vecMulVec (WithLp.ofLp a) (star (WithLp.ofLp b)) =
      ∑ k : Fin 4, zPhase k • Matrix.vecMulVec
        (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))
        (star (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))) ∧
    ∀ k : Fin 4, ‖(2⁻¹ : ℂ) • (a + zPhase k • b)‖ ≤ 1 := by
  constructor
  · ext i j
    change a.ofLp i * star (b.ofLp j) = ∑ k : Fin 4, zPhase k *
      ((2⁻¹ : ℂ) * (a.ofLp i + zPhase k * b.ofLp i) *
        star ((2⁻¹ : ℂ) * (a.ofLp j + zPhase k * b.ofLp j)))
    exact scalar_polarization _ _ _ _
  · intro k
    rw [norm_smul]
    have hz : ‖zPhase k • b‖ = ‖b‖ := by simp [norm_smul, norm_zPhase]
    have hsum : ‖a + zPhase k • b‖ ≤ 2 := by
      calc
        _ ≤ ‖a‖ + ‖zPhase k • b‖ := norm_add_le _ _
        _ ≤ 2 := by rw [hz]; linarith
    norm_num [norm_inv]
    linarith

end QSampVerif


set_option autoImplicit false

namespace QSampVerif
open scoped Matrix

lemma operator_polarization {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) :
    A * X * Bᴴ = ∑ k : Fin 4, zPhase k •
      (((2⁻¹ : ℂ) • (A + zPhase k • B)) * X *
        ((2⁻¹ : ℂ) • (A + zPhase k • B))ᴴ) := by
  simp [Fin.sum_univ_four, zPhase, pow_succ, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma operator_polarization_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) :
    (∑ k : Fin 4,
      (((2⁻¹ : ℂ) • (A + zPhase k • B)) * X *
        ((2⁻¹ : ℂ) • (A + zPhase k • B))ᴴ)) = A * X * Aᴴ + B * X * Bᴴ := by
  simp [Fin.sum_univ_four, zPhase, pow_succ, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]

lemma refMass_add_phase_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Matrix ι ι ℂ) (A B : Matrix κ ι ℂ) :
    (∑ k : Fin 4, refMass Ω ((2⁻¹ : ℂ) • (A + zPhase k • B))) =
      refMass Ω A + refMass Ω B := by
  have h := congrArg (fun M : Matrix κ κ ℂ => (Matrix.trace M).re)
    (operator_polarization_mass A B Ω)
  simpa only [refMass, Matrix.trace_sum, Complex.re_sum, Matrix.trace_add,
    Complex.add_re] using h

lemma refMass_real_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Ω : Matrix ι ι ℂ) (A : Matrix κ ι ℂ) (r : ℝ) :
    refMass Ω ((r : ℂ) • A) = r ^ 2 * refMass Ω A := by
  have hs : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [refMass, Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  ring

lemma balanced_mass_scalar (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    let r := (y / x) ^ (1 / 4 : ℝ)
    r ^ 2 * x + (r⁻¹) ^ 2 * y = 2 * Real.sqrt (x * y) := by
  dsimp only
  let r := (y / x) ^ (1 / 4 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hy hx) _
  have hr4 : r ^ 4 = y / x := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (div_pos hy hx))]
    norm_num
  have hmul : (r ^ 2 * x) ^ 2 = x * y := by
    have h : r ^ 4 * x = y := (eq_div_iff (ne_of_gt hx)).mp hr4
    nlinarith [h]
  have hs : Real.sqrt (x * y) = r ^ 2 * x := by
    rw [← hmul, Real.sqrt_sq (by positivity : 0 ≤ r ^ 2 * x)]
  change r ^ 2 * x + (r⁻¹) ^ 2 * y = _
  rw [hs]
  have h : r ^ 4 * x = y := (eq_div_iff (ne_of_gt hx)).mp hr4
  rw [← h]
  field_simp [ne_of_gt hr]
  <;> ring

end QSampVerif


set_option autoImplicit false

namespace QSampVerif

open scoped Matrix ComplexOrder

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 13.11 (Balanced operator polarization), (477), p.178 (PDF 179).

For operators `A_i, A_j` with common input and output spaces with `µ_i = µ(A_i) > 0` and
`µ_j = µ(A_j) > 0`, let `α = (µ_j/µ_i)^{1/4}` and `B_z = (α A_i + z α^{−1} A_j)/2`. Then for every
operator `X` on the input space, `A_i X A_j† = Σ_{z ∈ Z} z B_z X B_z†`, and
`Σ_{z ∈ Z} µ(B_z) = 2√(µ_i µ_j)`.

**Formalization Note.** `µ(A) = Tr(A Ω A†)` (`refMass`); the reference `Ω` is any positive
semidefinite operator on the input space (the paper's `Ω` is a density operator). -/
theorem balanced_operator_polarization {ι κ : Type*} [Fintype ι] [Fintype κ] (Ω : Matrix ι ι ℂ) (hΩ : Ω.PosSemidef)
    (Ai Aj : Matrix κ ι ℂ) (hi : 0 < refMass Ω Ai) (hj : 0 < refMass Ω Aj)
    (X : Matrix ι ι ℂ) :
    Ai * X * Ajᴴ = ∑ k : Fin 4, zPhase k •
      (((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) * X *
        ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj))ᴴ) ∧
    ∑ k : Fin 4, refMass Ω
      ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) =
      2 * Real.sqrt (refMass Ω Ai * refMass Ω Aj)  := by
  let r : ℝ := (refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hj hi) _
  change Ai * X * Ajᴴ = ∑ k : Fin 4, zPhase k •
    (((2⁻¹ : ℂ) • ((r : ℂ) • Ai + zPhase k • ((r⁻¹ : ℝ) : ℂ) • Aj)) * X *
      ((2⁻¹ : ℂ) • ((r : ℂ) • Ai + zPhase k • ((r⁻¹ : ℝ) : ℂ) • Aj))ᴴ) ∧
    (∑ k : Fin 4, refMass Ω
      ((2⁻¹ : ℂ) • ((r : ℂ) • Ai + zPhase k • ((r⁻¹ : ℝ) : ℂ) • Aj))) = _
  constructor
  · have h := operator_polarization ((r : ℂ) • Ai) (((r⁻¹ : ℝ) : ℂ) • Aj) X
    simpa only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt hr), inv_mul_cancel₀ (ne_of_gt hr),
      Complex.ofReal_one, one_smul] using h
  · rw [refMass_add_phase_sum, refMass_real_smul, refMass_real_smul]
    exact balanced_mass_scalar _ _ hi hj


end QSampVerif

open QSampVerif
open scoped Matrix
open scoped ComplexOrder

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (Ω : Matrix ι ι ℂ) (hΩ : Ω.PosSemidef)
    (Ai Aj : Matrix κ ι ℂ) (hi : 0 < refMass Ω Ai) (hj : 0 < refMass Ω Aj)
    (X : Matrix ι ι ℂ) :
    Ai * X * Ajᴴ = ∑ k : Fin 4, zPhase k •
      (((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) * X *
        ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj))ᴴ) ∧
    ∑ k : Fin 4, refMass Ω
      ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) =
      2 * Real.sqrt (refMass Ω Ai * refMass Ω Aj)  := QSampVerif.balanced_operator_polarization Ω hΩ Ai Aj hi hj X
