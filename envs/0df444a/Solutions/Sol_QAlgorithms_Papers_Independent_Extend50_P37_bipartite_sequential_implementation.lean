-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P37.bipartite_sequential_implementation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:12:40.01647+00:00
-- url     : https://prove2.me/submissions/29919f84-81b1-4818-a0a7-daecdbee7e6e

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37
noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

theorem s111a_perm_apply {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (s : Equiv.Perm (Fin n))
    (x y : Fin n → I) : perm I n s x y = if x = y ∘ s.symm then 1 else 0 := by
  unfold perm Schur.tensorPermutation
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i
    have := congrFun h i
    exact (Fintype.equivFin I).injective (by simpa using this)
  · intro h; subst h; rfl

theorem s111a_perm_mul {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (s t : Equiv.Perm (Fin n)) :
    perm I n s * perm I n t = perm I n (s * t) := by
  ext x y
  rw [Matrix.mul_apply]
  simp_rw [s111a_perm_apply]
  rw [Finset.sum_eq_single (y ∘ t.symm)]
  · simp only [if_true, mul_one]
    congr 1
  · intro b _ hb; simp [hb]
  · simp

theorem s111a_perm_one {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) :
    perm I n 1 = 1 := by
  ext x y
  rw [s111a_perm_apply, Matrix.one_apply]
  have : y ∘ (1 : Equiv.Perm (Fin n)).symm = y := rfl
  rw [this]

theorem s111a_perm_conjT {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (s : Equiv.Perm (Fin n)) :
    (perm I n s)ᴴ = perm I n s⁻¹ := by
  ext x y
  rw [Matrix.conjTranspose_apply, s111a_perm_apply, s111a_perm_apply]
  have : (y = x ∘ s.symm) ↔ (x = y ∘ (s⁻¹).symm) := by
    constructor
    · intro h; subst h; funext i; simp [Equiv.Perm.inv_def]
    · intro h; subst h; funext i; simp [Equiv.Perm.inv_def]
  by_cases h : y = x ∘ s.symm
  · rw [if_pos h, if_pos (this.mp h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; simp

theorem s111a_univ_fin_two :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  decide

theorem s111a_sector_false (I : Type*) [Fintype I] [DecidableEq I] :
    permutationSector I 2 false = (1/2 : ℂ) • (1 + perm I 2 (Equiv.swap 0 1)) := by
  unfold permutationSector
  rw [s111a_univ_fin_two, Finset.sum_pair (by decide)]
  simp [s111a_perm_one]

theorem s111a_sector_true (I : Type*) [Fintype I] [DecidableEq I] :
    permutationSector I 2 true = (1/2 : ℂ) • (1 - perm I 2 (Equiv.swap 0 1)) := by
  unfold permutationSector
  rw [s111a_univ_fin_two, Finset.sum_pair (by decide)]
  simp [s111a_perm_one, sub_eq_add_neg]

theorem s111a_swap_sq (I : Type*) [Fintype I] [DecidableEq I] :
    perm I 2 (Equiv.swap 0 1) * perm I 2 (Equiv.swap 0 1) = 1 := by
  rw [s111a_perm_mul, Equiv.swap_mul_self, s111a_perm_one]

theorem s111a_swap_herm (I : Type*) [Fintype I] [DecidableEq I] :
    (perm I 2 (Equiv.swap 0 1))ᴴ = perm I 2 (Equiv.swap 0 1) := by
  rw [s111a_perm_conjT, Equiv.swap_inv]

end QAlgorithms.Papers.Independent.Extend50.P37

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P37

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {O : Type*} [MeasurableSpace O]
    (A : StarSubalgebra ℂ (Mat I))
    (Mplus Mminus : Measurements.OperatorPOVM (Fin 2 → I) O)
    (hp : InAlgebra Mplus.operator (tensorAlg 2 (A : Set (Mat I))))
    (hm : InAlgebra Mminus.operator (tensorAlg 2 (A : Set (Mat I)))) :
    ∃ N : Measurements.OperatorPOVM (Fin 2 → I) O,
      (∀ B, MeasurableSet B → N.operator B =
        permutationSector I 2 false * Mplus.operator B * permutationSector I 2 false +
        permutationSector I 2 true * Mminus.operator B * permutationSector I 2 true) ∧
      ∀ rho, IsDensityMatrix rho → ∀ B, MeasurableSet B →
        effectProb (N.operator B) rho =
          effectProb (Mplus.operator B) (permutationSector I 2 false * rho * permutationSector I 2 false) +
          effectProb (Mminus.operator B) (permutationSector I 2 true * rho * permutationSector I 2 true) := by
  set P := permutationSector I 2 false with hP
  set Q := permutationSector I 2 true with hQ
  set S := perm I 2 (Equiv.swap 0 1) with hS
  have hSS : S * S = 1 := s111a_swap_sq I
  have hSH : Sᴴ = S := s111a_swap_herm I
  have hP' : P = (1/2 : ℂ) • (1 + S) := s111a_sector_false I
  have hQ' : Q = (1/2 : ℂ) • (1 - S) := s111a_sector_true I
  have hPH : Pᴴ = P := by
    rw [hP', Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hSH]; simp
  have hQH : Qᴴ = Q := by
    rw [hQ', Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hSH]; simp
  have htot : P * 1 * P + Q * 1 * Q = 1 := by
    rw [hP', hQ']
    simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hSS, smul_smul]
    rw [← sub_eq_zero]
    module
  refine ⟨{ operator := fun B => P * Mplus.operator B * P + Q * Mminus.operator B * Q,
            empty := by simp [Mplus.empty, Mminus.empty],
            total := by simp only [Mplus.total, Mminus.total]; exact htot,
            positive := ?_, additive := ?_ }, fun B _ => rfl, ?_⟩
  · intro B hB
    have h1 := (Mplus.positive B hB).mul_mul_conjTranspose_same P
    have h2 := (Mminus.positive B hB).mul_mul_conjTranspose_same Q
    rw [hPH] at h1; rw [hQH] at h2
    exact h1.add h2
  · intro B hB hd
    have h1 := ((Mplus.additive B hB hd).mul_left P).mul_right P
    have h2 := ((Mminus.additive B hB hd).mul_left Q).mul_right Q
    exact h1.add h2
  · intro rho _ B _
    simp only [effectProb]
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    congr 2
    · rw [show P * Mplus.operator B * P * rho = P * (Mplus.operator B * P * rho) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    · rw [show Q * Mminus.operator B * Q * rho = Q * (Mminus.operator B * Q * rho) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
