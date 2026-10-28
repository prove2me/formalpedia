-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.rho_star_binomial_orders
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:23:56.26808+00:00
-- url     : https://prove2.me/submissions/7b6bba62-43aa-49c2-8fe8-58a1070e38e6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

def RSB_c : ℕ → ℚ
  | 0 => 1
  | (a+1) => RSB_c a * (2*a+1)/(2*a+2)

lemma RSB_c_eq (a : ℕ) :
    ((Nat.factorial (2*a) : ℝ) / (4^a * (Nat.factorial a : ℝ)^2)) = (RSB_c a : ℝ) := by
  induction a with
  | zero => simp [RSB_c]
  | succ a ih =>
    rw [show 2*(a+1) = 2*a+1+1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, RSB_c]
    push_cast
    rw [← ih]
    have h1 : (0:ℝ) < (Nat.factorial (2*a) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0:ℝ) < (Nat.factorial a : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp
    ring

def RSB_bq (m : ℕ) (x : ℚ) : ℚ := x * ∑ a ∈ Finset.range m, RSB_c a * (1-x)^a

lemma RSB_bin_eq (m : ℕ) (x : ℚ) : binomial m (x:ℝ) = (RSB_bq m x : ℝ) := by
  simp [binomial, RSB_bq, RSB_c_eq]

lemma RSB_succ (m : ℕ) (x : ℝ) : binomial (m+1) x = binomial m x +
    x * (((Nat.factorial (2*m) : ℝ) / (4^m * (Nat.factorial m : ℝ)^2)) * (1-x)^m) := by
  simp only [binomial, Finset.sum_range_succ]; ring

lemma RSB_mono (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Monotone (fun m => binomial m x) := by
  apply monotone_nat_of_le_succ
  intro m
  simp only [RSB_succ]
  have : 0 ≤ 1 - x := by linarith
  have : 0 ≤ x * (((Nat.factorial (2*m) : ℝ) / (4^m * (Nat.factorial m : ℝ)^2)) * (1-x)^m) := by
    positivity
  linarith

lemma RSB_q1 : RSB_bq 29 (1/9) + 5 * RSB_bq 29 (1/36) < 1 := by decide +kernel
lemma RSB_q2 : 1 < RSB_bq 30 (1/9) + 5 * RSB_bq 30 (1/36) := by decide +kernel
lemma RSB_q3 : 5 * RSB_bq 12 (1/16) < 1 := by decide +kernel
lemma RSB_q4 : 1 < 5 * RSB_bq 13 (1/16) := by decide +kernel


def RSB_u : Fin 4 → Fin 3 → Fin 3 → ℝ :=
  ![![![1,0,0],![0,0,0],![0,Real.sqrt 2,0]],
    ![![0,1,0],![0,0,Real.sqrt 2],![0,0,0]],
    ![![0,0,Real.sqrt 2],![-1,0,0],![0,0,0]],
    ![![0,0,0],![0,1,0],![-Real.sqrt 2,0,0]]]

def RSB_Wt : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![![1,0,0],![0,1,0],![0,0,2]],
    ![![0,0,0],![0,0,Real.sqrt 2],![-Real.sqrt 2,0,0]],
    ![![0,Real.sqrt 2,0],![0,0,0],![0,0,0]]],
   ![![![0,0,-Real.sqrt 2],![0,0,0],![0,Real.sqrt 2,0]],
    ![![1,0,0],![0,1,0],![0,0,2]],
    ![![0,0,0],![-Real.sqrt 2,0,0],![0,0,0]]],
   ![![![0,0,0],![Real.sqrt 2,0,0],![0,0,0]],
    ![![0,-Real.sqrt 2,0],![0,0,0],![0,0,0]],
    ![![2,0,0],![0,2,0],![0,0,0]]]]

def RSB_Ct : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,4,0],![0,0,0],![0,0,0]],
    ![![0,0,2],![0,0,0],![0,-2,0]]],
   ![![![0,0,0],![4,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,4]],
    ![![0,0,0],![0,0,2],![-2,0,0]]],
   ![![![0,0,0],![0,0,-2],![2,0,0]],
    ![![0,0,-2],![0,0,0],![0,2,0]],
    ![![4,0,0],![0,4,0],![0,0,8]]]]

def RSB_CYt : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,36,0],![0,0,0],![0,0,0]],
    ![![0,0,18],![0,0,0],![0,-18,0]]],
   ![![![0,0,0],![36,0,0],![0,0,0]],
    ![![6,0,0],![0,6,0],![0,0,-12]],
    ![![0,0,0],![0,0,18],![-18,0,0]]],
   ![![![0,0,0],![0,0,-18],![18,0,0]],
    ![![0,0,-18],![0,0,0],![0,18,0]],
    ![![-12,0,0],![0,-12,0],![0,0,24]]]]

def RSB_W : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ := fun a b => RSB_Wt a.1 a.2 b.1 b.2
def RSB_C : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ := fun a b => RSB_Ct a.1 a.2 b.1 b.2
def RSB_CY : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ := fun a b => RSB_CYt a.1 a.2 b.1 b.2
def RSB_WY : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ := fun a b =>
  3 * RSB_W a b - 4 * ((if a.1 = a.2 then 1 else 0) * (if b.1 = b.2 then 1 else 0))

theorem RSB_sv (k : Fin 4) (p : Fin 3 × Fin 3) :
    starVectors k p = (((Real.sqrt 3)⁻¹ * RSB_u k p.1 p.2 : ℝ) : ℂ) := by
  obtain ⟨i, j⟩ := p
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [starVectors, RSB_u, QAlgorithms.ket]

lemma RSB_uW (p1 p2 q1 q2 : Fin 3) :
    ∑ k, RSB_u k p1 p2 * RSB_u k q1 q2 = RSB_Wt p1 q1 p2 q2 := by
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp [Fin.sum_univ_four, RSB_u, RSB_Wt]

lemma RSB_rho (p q : Fin 3 × Fin 3) :
    rhoStar p q = ((RSB_Wt p.1 q.1 p.2 q.2 / 12 : ℝ) : ℂ) := by
  have h3 : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1/3 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hk : ∀ k, starVectors k p * conj (starVectors k q) =
      ((1/3 * (RSB_u k p.1 p.2 * RSB_u k q.1 q.2) : ℝ) : ℂ) := by
    intro k
    rw [RSB_sv, RSB_sv, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    linear_combination (RSB_u k p.1 p.2 * RSB_u k q.1 q.2) * h3
  simp only [rhoStar, Matrix.smul_apply, Matrix.sum_apply, outer, hk, smul_eq_mul]
  rw [← RSB_uW]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma RSB_rm (X : Bip 3 3) (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ)
    (h : ∀ a b, realign X a b = ((A a b : ℝ) : ℂ)) (k : ℕ) :
    rMoment X k = ((A * Aᵀ)^k).trace := by
  have h1 : realign X * (realign X)ᴴ = (Complex.ofRealHom.mapMatrix) (A * Aᵀ) := by
    rw [map_mul]
    congr 1
    · ext a b; simp [h]
    · ext a b; simp [Matrix.conjTranspose_apply, h]
  rw [rMoment, powerTrace, h1, ← map_pow, RingHom.mapMatrix_apply,
    ← AddMonoidHom.map_trace]
  simp

lemma RSB_WWC : RSB_W * RSB_Wᵀ = RSB_C := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, RSB_W, RSB_Wt,
      RSB_C, RSB_Ct] <;> norm_num

lemma RSB_trC : RSB_C.trace = 36 := by
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_three, RSB_C, RSB_Ct]; norm_num

lemma RSB_trC2 : (RSB_C ^ 2).trace = 336 := by
  simp [sq, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
    RSB_C, RSB_Ct]; norm_num


lemma RSB_rhoW (a b : Fin 3 × Fin 3) :
    realign rhoStar a b = ((((1/12 : ℝ) • RSB_W) a b : ℝ) : ℂ) := by
  simp only [realign, RSB_rho, RSB_W, Matrix.smul_apply, smul_eq_mul]
  congr 1; ring

lemma RSB_smul_gram (c : ℝ) (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) :
    (c • A) * (c • A)ᵀ = (c * c) • (A * Aᵀ) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma RSB_m1 : rMoment rhoStar 1 = 1/4 := by
  rw [RSB_rm _ _ RSB_rhoW, RSB_smul_gram, RSB_WWC, pow_one, Matrix.trace_smul, RSB_trC]
  norm_num

lemma RSB_m2 : rMoment rhoStar 2 = 7/432 := by
  rw [RSB_rm _ _ RSB_rhoW, RSB_smul_gram, RSB_WWC, smul_pow, Matrix.trace_smul, RSB_trC2]
  norm_num

lemma RSB_mass : mass rhoStar = 1 := by
  simp [mass, powerTrace, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_three, RSB_rho,
    RSB_Wt]
  norm_num

lemma RSB_mA : marginalA rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [marginalA, Fin.sum_univ_three, RSB_rho, RSB_Wt] <;> norm_num

lemma RSB_mB : marginalB rhoStar = (1/3 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [marginalB, Fin.sum_univ_three, RSB_rho, RSB_Wt] <;> norm_num

lemma RSB_G : G rhoStar = 4/9 := by
  have hp : powerTrace ((1/3:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 2 = 1/3 := by
    simp [powerTrace, smul_pow, Matrix.trace_smul]; norm_num
  simp only [G, purityA, purityB, RSB_mA, RSB_mB, hp, RSB_mass]; norm_num

lemma RSB_Yre (a b : Fin 3 × Fin 3) :
    realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) a b =
      ((((1/24 : ℝ) • RSB_WY) a b : ℝ) : ℂ) := by
  have hs : Real.sqrt (4/9) = 2/3 := by
    rw [show (4/9:ℝ) = (2/3)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [RSB_G, hs]
  simp only [realign, centered, Matrix.smul_apply, Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    RSB_mA, RSB_mB, RSB_mass, Matrix.one_apply, RSB_rho, RSB_WY, RSB_W, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

lemma RSB_WYC : RSB_WY * RSB_WYᵀ = RSB_CY := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, RSB_WY, RSB_W, RSB_Wt,
      RSB_CY, RSB_CYt] <;> norm_num <;>
    linarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

lemma RSB_trCY : RSB_CY.trace = 180 := by
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_three, RSB_CY, RSB_CYt]; norm_num

lemma RSB_trCY2 : (RSB_CY ^ 2).trace = 6480 := by
  simp [sq, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
    RSB_CY, RSB_CYt]; norm_num

lemma RSB_y1 : rMoment (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) 1 = 5/16 := by
  rw [RSB_rm _ _ RSB_Yre, RSB_smul_gram, RSB_WYC, pow_one, Matrix.trace_smul, RSB_trCY]
  norm_num

lemma RSB_y2 : rMoment (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar) 2 = 5/256 := by
  rw [RSB_rm _ _ RSB_Yre, RSB_smul_gram, RSB_WYC, smul_pow, Matrix.trace_smul, RSB_trCY2]
  norm_num

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
/-- §6.5 unnumbered: minimal binomial orders for rhoStar; arXiv:2609.29471v1, PDF pp.46, 47. -/
theorem solution  :
    binomial 29 (1/9)+5*binomial 29 (1/36)<1 ∧
    1<binomial 30 (1/9)+5*binomial 30 (1/36) ∧
    5*binomial 12 (1/16)<1 ∧ 1<5*binomial 13 (1/16) ∧
    (∀ m : ℕ, 1 ≤ m → m<30 → binomial m (1/9)+5*binomial m (1/36)≤1) ∧
    (∀ m : ℕ, 30 ≤ m → 1<binomial m (1/9)+5*binomial m (1/36)) ∧
    (∀ m : ℕ, 1 ≤ m → m<13 → 5*binomial m (1/16)≤1) ∧
    (∀ m : ℕ, 13 ≤ m → 1<5*binomial m (1/16)) ∧
    rMoment rhoStar 1=1/4 ∧ rMoment rhoStar 2=7/432 ∧
    rMoment rhoStar 1^3<rMoment rhoStar 2 ∧
    (let Y := ((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar
     rMoment Y 1=5/16 ∧ rMoment Y 2=5/256 ∧ rMoment Y 1^3/rMoment Y 2=25/16) := by
  have e9 : ∀ m, binomial m (1/9) = (RSB_bq m (1/9) : ℝ) := fun m => by
    rw [← RSB_bin_eq]; norm_num
  have e36 : ∀ m, binomial m (1/36) = (RSB_bq m (1/36) : ℝ) := fun m => by
    rw [← RSB_bin_eq]; norm_num
  have e16 : ∀ m, binomial m (1/16) = (RSB_bq m (1/16) : ℝ) := fun m => by
    rw [← RSB_bin_eq]; norm_num
  have q1 : binomial 29 (1/9) + 5 * binomial 29 (1/36) < 1 := by
    rw [e9, e36]; exact_mod_cast RSB_q1
  have q2 : 1 < binomial 30 (1/9) + 5 * binomial 30 (1/36) := by
    rw [e9, e36]; exact_mod_cast RSB_q2
  have q3 : 5 * binomial 12 (1/16) < 1 := by
    rw [e16]; exact_mod_cast RSB_q3
  have q4 : 1 < 5 * binomial 13 (1/16) := by
    rw [e16]; exact_mod_cast RSB_q4
  have M9 := RSB_mono (1/9) (by norm_num) (by norm_num)
  have M36 := RSB_mono (1/36) (by norm_num) (by norm_num)
  have M16 := RSB_mono (1/16) (by norm_num) (by norm_num)
  refine ⟨q1, q2, q3, q4, ?_, ?_, ?_, ?_, RSB_m1, RSB_m2, ?_, ?_⟩
  · intro m _ hm
    have a := M9 (show m ≤ 29 by omega)
    have b := M36 (show m ≤ 29 by omega)
    simp only at a b
    linarith
  · intro m hm
    have a := M9 hm
    have b := M36 hm
    simp only at a b
    linarith
  · intro m _ hm
    have a := M16 (show m ≤ 12 by omega)
    simp only at a
    linarith
  · intro m hm
    have a := M16 hm
    simp only at a
    linarith
  · rw [RSB_m1, RSB_m2]; norm_num
  · dsimp only
    refine ⟨RSB_y1, RSB_y2, ?_⟩
    rw [RSB_y1, RSB_y2]; norm_num

end
