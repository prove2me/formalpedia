-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P01.embeddingCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:03:35.091423+00:00
-- url     : https://prove2.me/submissions/646632d6-d3d5-454e-9ac3-2dccd15ef437

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

open scoped Matrix ComplexConjugate

noncomputable section

lemma g52_s2 : ((Real.sqrt 2 / 4 : ℝ) : ℂ) * ((Real.sqrt 2 / 4 : ℝ) : ℂ) = 1 / 8 := by
  rw [← Complex.ofReal_mul, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; push_cast; norm_num

lemma g52_s2' : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; push_cast; norm_num

lemma g52_c2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma g52_pk {ι : Type*} [DecidableEq ι] (k a b : ι) :
    QAlgorithms.pureDensity (QAlgorithms.ket k) a b = if a = k ∧ b = k then 1 else 0 := by
  simp only [QAlgorithms.pureDensity, QAlgorithms.ket, Matrix.of_apply]
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp [ha, hb, PiLp.single_apply]

lemma g52_pp (a b : Fin 2) :
    QAlgorithms.pureDensity QAlgorithms.Papers.Independent.Frontier30.P01.plusVector a b = 1 / 2 := by
  simp only [QAlgorithms.pureDensity, QAlgorithms.Papers.Independent.Frontier30.P01.plusVector,
    Matrix.of_apply, Complex.conj_ofReal]
  exact g52_s2'

set_option maxHeartbeats 4000000 in
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent
  QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P01 in
theorem solution :
    ‖counterVector‖ = 1 ∧
    qqqVector (fun x => Complex.normSq (counterVector x)) = counterVector ∧
    traceLeft (Information100.P34.dephasing (pureDensity counterVector)) =
      Dependency50.P24.idealCCQ ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    measureAB (traceLeft (pureDensity counterVector)) =
      (1/2 : ℂ) • Matrix.kronecker (pureDensity (ket (0,0))) (pureDensity plusVector) +
      (1/2 : ℂ) • Matrix.kronecker (pureDensity (ket (1,1)))
        ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    ¬ (∃ tau : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix tau ∧
      measureAB (traceLeft (pureDensity counterVector)) = Dependency50.P24.idealCCQ tau) := by
  have hs : (0:ℝ) ≤ Real.sqrt 2 / 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [counterVector, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff,
      abs_of_nonneg (Real.sqrt_nonneg 2), div_pow]
    norm_num
  · ext x
    simp only [qqqVector, counterVector]
    split_ifs <;> simp [Complex.normSq_apply] <;> norm_num
  · ext ⟨⟨i, j⟩, e⟩ ⟨⟨i', j'⟩, e'⟩
    fin_cases i <;> fin_cases j <;> fin_cases e <;> fin_cases i' <;> fin_cases j' <;> fin_cases e' <;>
      simp [traceLeft, Information100.P34.dephasing, pureDensity, counterVector,
        Dependency50.P24.idealCCQ, Fin.sum_univ_two, Matrix.diagonal_apply, map_ofNat] <;>
      ring_nf <;> simp [g52_c2] <;> norm_num
  · ext ⟨⟨i, j⟩, e⟩ ⟨⟨i', j'⟩, e'⟩
    fin_cases i <;> fin_cases j <;> fin_cases e <;> fin_cases i' <;> fin_cases j' <;> fin_cases e' <;>
      simp [traceLeft, measureAB, g52_pk, g52_pp, Matrix.kroneckerMap_apply, Fin.sum_univ_two] <;>
      simp [pureDensity, counterVector, map_ofNat] <;> ring_nf <;> simp [g52_c2] <;> norm_num
  · rintro ⟨tau, _, h⟩
    have h1 := congrFun (congrFun h ((0, 0), 0)) ((0, 0), 1)
    have h2 := congrFun (congrFun h ((1, 1), 0)) ((1, 1), 1)
    simp [traceLeft, measureAB, pureDensity, counterVector, Dependency50.P24.idealCCQ,
      Fin.sum_univ_two, map_ofNat] at h1 h2
    ring_nf at h1 h2
    simp [g52_c2] at h1 h2
    rw [h2] at h1
    norm_num at h1
