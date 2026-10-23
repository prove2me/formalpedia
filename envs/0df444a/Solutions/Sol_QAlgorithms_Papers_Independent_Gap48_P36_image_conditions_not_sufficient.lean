-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.image_conditions_not_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:21:29.415933+00:00
-- url     : https://prove2.me/submissions/800feb4e-7f6a-4530-a4f1-462cf57bbe73

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix Complex

def x8P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

def x8k : Fin 4 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

def x8z : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, I, -I], ![1, -I, 1, I], ![1, I, -I, 1]]

theorem x8_prod (m n : Fin 4) : (x8P m)ᴴ * x8P n = x8z m n • x8P (x8k m n) := by
  fin_cases m <;> fin_cases n <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [x8P, x8k, x8z, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

theorem x8_unit (k : Fin 4) : (x8P k)ᴴ * x8P k = 1 := by
  rw [x8_prod]
  fin_cases k <;> simp [x8z, x8k, x8P]

theorem x8_tr (k : Fin 4) : (x8P k).trace = if k = 0 then 2 else 0 := by
  fin_cases k <;> simp [x8P, trace, Fin.sum_univ_two] <;> norm_num

theorem x8_orth (j k : Fin 4) :
    ((x8P j)ᴴ * x8P k).trace = if j = k then 2 else 0 := by
  rw [x8_prod, trace_smul, x8_tr]
  fin_cases j <;> fin_cases k <;> simp [x8k, x8z]

def x8T : UnitaryBasis (Fin 2) (Fin (2 ^ 2)) where
  matrix := x8P
  identityLabel := 0
  cardinality := by simp
  identity := rfl
  unitary := x8_unit
  orthogonal := fun j k => by rw [x8_orth]; simp

theorem x8_phase : PhaseClosed x8T := by
  intro m n
  refine ⟨x8k m n, x8z m n, ?_, x8_prod m n⟩
  fin_cases m <;> fin_cases n <;> simp [x8z]

def x8W : Matrix (Fin 4) (Fin 2) ℂ := !![1, 0; -I, 0; 0, 1; 0, 1]

def x8γ : Matrix (Fin 4) (Fin 4) ℂ := (1 / 4 : ℂ) • (x8W * x8Wᴴ)

theorem x8_WW : x8Wᴴ * x8W = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [x8W, mul_apply, Fin.sum_univ_four, conjTranspose_apply] <;> norm_num

def x8tbl : Fin 4 → Fin 4 → ℂ :=
  ![![1/4, I/4, 0, 0], ![-I/4, 1/4, 0, 0], ![0, 0, 1/4, 1/4], ![0, 0, 1/4, 1/4]]

theorem x8_γ_apply (j k : Fin 4) : x8γ j k = x8tbl j k := by
  rw [x8γ, Matrix.smul_apply, mul_apply]
  simp only [conjTranspose_apply, Fin.sum_univ_two]
  fin_cases j <;> fin_cases k <;> simp [x8W, x8tbl] <;> ring

theorem x8_scale (T : K → Matrix A A ℂ) (c : K → ℂ) (rho : Matrix A A ℂ) (k k' : K) :
    complementaryChannel (indexedKrausDilation (fun k => c k • T k)) rho k k' =
      c k * star (c k') * complementaryChannel (indexedKrausDilation T) rho k k' := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl
    fun a _ => ?_
  ring


theorem x8_w (T : UnitaryBasis A K) (psi : EuclideanSpace ℂ A) (j k : K) :
    noisyComplement T.matrix (pureDensity psi) j k = ((Fintype.card A : ℂ)⁻¹)^2 *
      ∑ b, (T.matrix j *ᵥ (fun i => psi i)) b * star ((T.matrix k *ᵥ (fun i => psi i)) b) := by
  unfold noisyComplement
  rw [x8_scale T.matrix (fun _ => (Fintype.card A : ℂ)⁻¹)]
  have : star ((Fintype.card A : ℂ)⁻¹) = (Fintype.card A : ℂ)⁻¹ := by simp
  rw [this, sq]
  congr 1
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, pureDensity, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    star_sum, star_mul']
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => ?_
  simp [RCLike.star_def]
  ring

theorem x8_main :
    ∃ d : ℕ, ∃ hd : 0 < d,
      ∃ T : UnitaryBasis (Fin d) (Fin (d^2)), PhaseClosed T ∧
      ∃ gamma : Matrix (Fin (d^2)) (Fin (d^2)) ℂ,
        ImageConditions d gamma ∧ gamma ∉ pureNoisyImage T.matrix := by
  refine ⟨2, by norm_num, x8T, x8_phase, x8γ, ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine (posSemidef_self_mul_conjTranspose x8W).smul ?_
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 4)
  · rw [x8γ, trace_smul, trace_mul_comm, x8_WW, trace_smul, trace_one]; simp; norm_num
  · rw [x8γ, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show x8W * x8Wᴴ * (x8W * x8Wᴴ) = x8W * (x8Wᴴ * x8W) * x8Wᴴ by simp [Matrix.mul_assoc],
      x8_WW]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    norm_num
  · rw [x8γ, smul_smul, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (by norm_num)), rank_self_mul_conjTranspose,
      ← rank_conjTranspose_mul_self, x8_WW,
      rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by norm_num)), rank_one]
    simp
  · intro k; rw [x8_γ_apply]; fin_cases k <;> simp [x8tbl] <;> norm_num
  · intro j k; rw [x8_γ_apply]; fin_cases j <;> fin_cases k <;> simp [x8tbl] <;> norm_num
  · refine ⟨fun j k => mul_nonneg (by norm_num) (Complex.normSq_nonneg _), fun j => ?_, fun k => ?_⟩
    · simp only [x8_γ_apply]
      fin_cases j <;> simp [x8tbl, Fin.sum_univ_four, Complex.normSq_apply] <;> norm_num
    · simp only [x8_γ_apply]
      fin_cases k <;> simp [x8tbl, Fin.sum_univ_four, Complex.normSq_apply] <;> norm_num
  · rintro ⟨psi, -, hpsi⟩
    have h := congrFun (congrFun hpsi 0) 1
    rw [x8_w] at h
    change x8γ 0 1 = _ at h
    rw [x8_γ_apply] at h
    have him := congrArg Complex.im h
    simp [x8tbl, x8T, x8P, mulVec, dotProduct, Fin.sum_univ_two] at him
    have e2 : ((2 : ℂ) ^ 2).im = 0 := by norm_num
    rw [e2] at him
    ring_nf at him
    norm_num at him

end QAlgorithms.Papers.Independent.Gap48.P36

open QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution :
    ∃ d : ℕ, ∃ hd : 0 < d,
      ∃ T : UnitaryBasis (Fin d) (Fin (d^2)), PhaseClosed T ∧
      ∃ gamma : Matrix (Fin (d^2)) (Fin (d^2)) ℂ,
        ImageConditions d gamma ∧ gamma ∉ pureNoisyImage T.matrix :=
  x8_main
