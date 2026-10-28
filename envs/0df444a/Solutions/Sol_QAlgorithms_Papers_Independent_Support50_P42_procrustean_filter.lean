-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.procrustean_filter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:42:30.47856+00:00
-- url     : https://prove2.me/submissions/34d89d89-0b76-475d-97cc-dbe48ba2465a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== P42PF =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory ProbabilityTheory
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50.P42
open Information100.P21 (Op Vec FiniteLOCC)
open Next46.P39 (rectAct)

namespace X4P42F
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

lemma rect_kron_diag {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (d : I → ℂ) (e : J → ℂ) (v : EuclideanSpace ℂ (I × J)) (z : I × J) :
    rectAct (Matrix.kronecker (diagonal d) (diagonal e)) v z = d z.1 * e z.2 * v z := by
  simp only [rectAct, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, PiLp.toLp_apply,
    mulVec_diagonal]

variable {d : ℕ} (c : Fin d → ℝ)

lemma la_le (i : Fin d) : leastAmplitude c ≤ c i :=
  csInf_le (Set.finite_range c).bddBelow ⟨i, rfl⟩

lemma la_nonneg [Nonempty (Fin d)] (hc : ∀ i, 0 ≤ c i) : 0 ≤ leastAmplitude c :=
  le_csInf (Set.range_nonempty c) (by rintro _ ⟨i, rfl⟩; exact hc i)

lemma ratio_mem [Nonempty (Fin d)] (hc : ∀ i, 0 ≤ c i) (i : Fin d) :
    0 ≤ leastAmplitude c / c i ∧ leastAmplitude c / c i ≤ 1 := by
  have h0 := la_nonneg c hc
  have h1 := la_le c i
  refine ⟨div_nonneg h0 (hc i), ?_⟩
  rcases (hc i).eq_or_lt with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · exact (div_le_one h).2 h1

lemma ratio_mul [Nonempty (Fin d)] (hc : ∀ i, 0 ≤ c i) (i : Fin d) :
    leastAmplitude c / c i * c i = leastAmplitude c := by
  rcases (hc i).eq_or_lt with h | h
  · have := la_le c i; have := la_nonneg c hc
    rw [← h]; simp; linarith
  · field_simp

lemma branch_eq [Nonempty (Fin d)] (hc : ∀ i, 0 ≤ c i) :
    aliceKetBranch (procrusteanSuccess c) (diagonalKet c) =
      WithLp.toLp 2 (fun z : Fin d × Fin d => if z.1 = z.2 then (leastAmplitude c : ℂ) else 0) := by
  ext z
  simp only [aliceKetBranch, procrusteanSuccess]
  rw [← diagonal_one, rect_kron_diag]
  simp only [diagonalKet, PiLp.toLp_apply, mul_one]
  split_ifs with h
  · rw [← Complex.ofReal_mul, ratio_mul c hc]
  · simp

theorem main (hd : 0<d)
    (hc : ∀ i, 0≤c i) (hnorm : ∑ i, (c i)^2=1) :
    IsKrausFamily (fun j : Fin 2 => if j=0 then procrusteanSuccess c else filterFailure c) ∧
    pureDensity (aliceKetBranch (procrusteanSuccess c) (diagonalKet c))=
      ((((d : ℝ)*(leastAmplitude c)^2 : ℝ)) : ℂ) • pureDensity (uniformKet d) ∧
    ‖aliceKetBranch (procrusteanSuccess c) (diagonalKet c)‖^2=(d : ℝ)*(leastAmplitude c)^2 ∧
    (0<leastAmplitude c →
      ((Real.sqrt ((d : ℝ)*(leastAmplitude c)^2))⁻¹ : ℂ) •
        aliceKetBranch (procrusteanSuccess c) (diagonalKet c)=uniformKet d) ∧
    (∀ p : ℝ, 0≤p → p≤1 →
      (2 : ℝ)*(leastAmplitude (fun i : Fin 2 => if i=0 then Real.sqrt (1-p) else Real.sqrt p))^2=
        procrusteanYield p) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Kraus completeness
    unfold IsKrausFamily
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false,
      procrusteanSuccess, filterFailure, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_add]
    rw [← diagonal_one]
    congr 1; funext i
    obtain ⟨h0, h1⟩ := ratio_mem c hc i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith),
      ← Complex.ofReal_add]
    simp; ring
  · rw [branch_eq c hc]
    ext z w
    simp only [pureDensity, Matrix.of_apply, PiLp.toLp_apply, uniformKet, Matrix.smul_apply,
      smul_eq_mul]
    split_ifs with h1 h2 <;> simp
    rw [← mul_inv]
    rw [show (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hdpos.le]; simp]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    push_cast
    field_simp
  · rw [branch_eq c hc, EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply]
    rw [Fintype.sum_prod_type]
    have : ∀ x : Fin d, ∑ y : Fin d, ‖(if (x, y).1 = (x, y).2 then (leastAmplitude c : ℂ) else 0)‖ ^ 2
        = (leastAmplitude c) ^ 2 := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [abs_of_nonneg (la_nonneg c hc)]
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    simp_rw [this]
    simp
  · intro hm
    rw [branch_eq c hc]
    ext z
    simp only [PiLp.smul_apply, PiLp.toLp_apply, uniformKet, smul_eq_mul]
    split_ifs with h
    · rw [Real.sqrt_mul hdpos.le, Real.sqrt_sq hm.le]
      have : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hdpos).ne'
      have : (leastAmplitude c : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    · simp
  · intro p hp hp1
    have hr : Set.range (fun i : Fin 2 => if i=0 then Real.sqrt (1-p) else Real.sqrt p) =
        {Real.sqrt (1-p), Real.sqrt p} := by
      ext x; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    rw [leastAmplitude, hr, csInf_pair, procrusteanYield]
    rcases le_total p (1 - p) with h | h
    · rw [min_eq_right (Real.sqrt_le_sqrt h), min_eq_left h, Real.sq_sqrt hp]
    · rw [min_eq_left (Real.sqrt_le_sqrt h), min_eq_right h, Real.sq_sqrt (by linarith)]

end X4P42F

theorem solution (d : ℕ) (hd : 0<d) (c : Fin d → ℝ)
    (hc : ∀ i, 0≤c i) (hnorm : ∑ i, (c i)^2=1) :
    IsKrausFamily (fun j : Fin 2 => if j=0 then procrusteanSuccess c else filterFailure c) ∧
    pureDensity (aliceKetBranch (procrusteanSuccess c) (diagonalKet c))=
      ((((d : ℝ)*(leastAmplitude c)^2 : ℝ)) : ℂ) • pureDensity (uniformKet d) ∧
    ‖aliceKetBranch (procrusteanSuccess c) (diagonalKet c)‖^2=(d : ℝ)*(leastAmplitude c)^2 ∧
    (0<leastAmplitude c →
      ((Real.sqrt ((d : ℝ)*(leastAmplitude c)^2))⁻¹ : ℂ) •
        aliceKetBranch (procrusteanSuccess c) (diagonalKet c)=uniformKet d) ∧
    (∀ p : ℝ, 0≤p → p≤1 →
      (2 : ℝ)*(leastAmplitude (fun i : Fin 2 => if i=0 then Real.sqrt (1-p) else Real.sqrt p))^2=
        procrusteanYield p) :=
  X4P42F.main c hd hc hnorm

end

#print axioms solution
