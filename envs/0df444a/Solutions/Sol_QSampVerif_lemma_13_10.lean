-- Prove2me | solution 1 for QSampVerif.lemma_13_10
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T14:49:39.132417+00:00
-- url     : https://prove2.me/submissions/233efa08-a3ec-454f-b7dc-553803f431b6

import Definitions.Def_QSampVerif_zPhase


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

open QSampVerif

theorem solution {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) :
    Matrix.vecMulVec (WithLp.ofLp a) (star (WithLp.ofLp b)) =
      ∑ k : Fin 4, zPhase k • Matrix.vecMulVec (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))
        (star (WithLp.ofLp ((2⁻¹ : ℂ) • (a + zPhase k • b)))) ∧
    ∀ k : Fin 4, ‖(2⁻¹ : ℂ) • (a + zPhase k • b)‖ ≤ 1  := QSampVerif.vector_polarization a b ha hb
