-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.cloner12_degradable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:09:31.467969+00:00
-- url     : https://prove2.me/submissions/c52214b3-fcb9-41b9-99b7-b02156f2614f

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

namespace X7S1

/-- Kraus channels with an arbitrary finite index type. -/
lemma chan_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    IsChannel (krausApply E) := by
  let σ := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (σ.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  · intro ρ
    unfold krausApply
    exact (Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)).symm

lemma kraus_comp {ι κ μ K L : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype K] [Fintype L]
    (E : K → Matrix κ ι ℂ) (F : L → Matrix μ κ ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply F (krausApply E ρ) = krausApply (fun p : K × L => F p.2 * E p.1) ρ := by
  unfold krausApply
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma chan_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {_i1 : DecidableEq ι} {_i2 : DecidableEq κ}
    (Φ : Superop ι κ) (Ψ : Superop κ μ) (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    IsChannel (Ψ ∘ Φ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  obtain ⟨n, F, hF, hΨF⟩ := hΨ
  have h : Ψ ∘ Φ = krausApply (fun p : Fin m × Fin n => F p.2 * E p.1) := by
    funext ρ
    simp only [Function.comp, hΦE, hΨF, kraus_comp]
  rw [h]
  apply chan_of_kraus
  rw [Fintype.sum_prod_type]
  unfold IsKrausFamily at hE hF
  rw [← hE]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Matrix.conjTranspose_mul]
  have : ∀ j : Fin n, (E k)ᴴ * (F j)ᴴ * (F j * E k) = (E k)ᴴ * ((F j)ᴴ * F j) * E k := by
    intro j; simp [Matrix.mul_assoc]
  simp only [this, ← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one]

lemma kraus_smul {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (z : ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply E (z • ρ) = z • krausApply E ρ := by
  unfold krausApply
  rw [Finset.smul_sum]
  simp [Matrix.mul_smul, Matrix.smul_mul]

lemma kraus_add {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    krausApply E (ρ + σ) = krausApply E ρ + krausApply E σ := by
  unfold krausApply
  rw [← Finset.sum_add_distrib]
  simp [Matrix.mul_add, Matrix.add_mul]

/-- The entrywise-conjugated Kraus family implements the transposed channel. -/
lemma kraus_conj_transpose {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply (fun k => (E k).map (starRingEnd ℂ)) ρᵀ = (krausApply E ρ)ᵀ := by
  unfold krausApply
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  show (E k).map (starRingEnd ℂ) * (ρᵀ * ((E k).map (starRingEnd ℂ))ᴴ) = _
  rw [show ((E k).map (starRingEnd ℂ))ᴴ = (E k)ᵀ from by
        ext i j; simp [Matrix.conjTranspose_apply],
      show (E k)ᴴᵀ = (E k).map (starRingEnd ℂ) from by
        ext i j; simp [Matrix.conjTranspose_apply]]

lemma conj_kraus_family {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ k, ((E k).map (starRingEnd ℂ))ᴴ * (E k).map (starRingEnd ℂ) = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) hE
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)] at h
  rw [← h]
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]

lemma chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) :
    ∃ G : Superop ι κ, IsChannel G ∧ ∀ ρ, G ρᵀ = (Φ ρ)ᵀ := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  refine ⟨krausApply (fun k => (E k).map (starRingEnd ℂ)), chan_of_kraus _ ?_, ?_⟩
  · exact conj_kraus_family E hE
  · intro ρ; rw [hΦE]; exact kraus_conj_transpose E ρ

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable IsIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace X7C12

def p : ℂ := ((Real.sqrt (2/3) : ℝ) : ℂ)
def q : ℂ := ((Real.sqrt (1/3) : ℝ) : ℂ)
def r : ℂ := ((Real.sqrt (1/2) : ℝ) : ℂ)

lemma hp : p * p = 2/3 := by
  unfold p; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
lemma hq : q * q = 1/3 := by
  unfold q; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
lemma hr : r * r = 1/2 := by
  unfold r; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
lemma hrp : r * p = q := by
  unfold r p q; rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num),
    show (1/2:ℝ) * (2/3) = 1/3 by norm_num]

def s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma hs2 : s ^ 2 = 2 := by
  unfold s; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
lemma hs3 : s ^ 3 = 2 * s := by rw [pow_succ, hs2]
lemma hs4 : s ^ 4 = 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num
lemma hs5 : s ^ 5 = 4 * s := by rw [pow_succ, hs4]
lemma hs6 : s ^ 6 = 8 := by rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hs2]; norm_num
lemma hq2 : q ^ 2 = 1/3 := by rw [sq, hq]
lemma hq3 : q ^ 3 = 1/3 * q := by rw [pow_succ, hq2]
lemma hq4 : q ^ 4 = 1/9 := by rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2]; norm_num
lemma hp' : p = s * q := by
  unfold p s q; rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
lemma hr' : r = s / 2 := by
  unfold r s
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [show (1/2 : ℝ) = 2 / 4 by norm_num, Real.sqrt_div' _ (by norm_num), h4]; push_cast; ring

lemma U_apply (b : Fin 3) (j : Fin 2) (k : Fin 2) :
    clonerDilation 1 2 (b, j) k =
      if b.val = k.val + j.val then (if k = j then p else q) else 0 := by
  have c00 : cloningCoefficient 1 2 0 0 = 2/3 := by norm_num [cloningCoefficient, Nat.factorial]
  have c01 : cloningCoefficient 1 2 0 1 = 1/3 := by norm_num [cloningCoefficient, Nat.factorial]
  have c10 : cloningCoefficient 1 2 1 0 = 1/3 := by norm_num [cloningCoefficient, Nat.factorial]
  have c11 : cloningCoefficient 1 2 1 1 = 2/3 := by norm_num [cloningCoefficient, Nat.factorial]
  have s00 : ((Real.sqrt (cloningCoefficient 1 2 0 0) : ℝ) : ℂ) = p := by rw [c00]; rfl
  have s01 : ((Real.sqrt (cloningCoefficient 1 2 0 1) : ℝ) : ℂ) = q := by rw [c01]; rfl
  have s10 : ((Real.sqrt (cloningCoefficient 1 2 1 0) : ℝ) : ℂ) = q := by rw [c10]; rfl
  have s11 : ((Real.sqrt (cloningCoefficient 1 2 1 1) : ℝ) : ℂ) = p := by rw [c11]; rfl
  fin_cases b <;> fin_cases j <;> fin_cases k <;>
    simp [clonerDilation, s00, s01, s10, s11]

lemma sp : (starRingEnd ℂ) p = p := by unfold p; simp
lemma sq : (starRingEnd ℂ) q = q := by unfold q; simp
lemma sr : (starRingEnd ℂ) r = r := by unfold r; simp

lemma iso : (clonerDilation 1 2)ᴴ * clonerDilation 1 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      U_apply, sp, sq] <;> linear_combination hp + hq

lemma rec_eq (X : Matrix (Fin 2) (Fin 2) ℂ) : receiverChannel (clonerDilation 1 2) X =
    !![p*p*X 0 0, p*q*X 0 1, 0; p*q*X 1 0, q*q*(X 0 0 + X 1 1), p*q*X 0 1;
      0, p*q*X 1 0, p*p*X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [receiverChannel, traceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, U_apply, sp, sq] <;> ring

lemma comp_eq (X : Matrix (Fin 2) (Fin 2) ℂ) : complementaryChannel (clonerDilation 1 2) X =
    !![p*p*X 0 0 + q*q*X 1 1, q*q*X 1 0; q*q*X 0 1, q*q*X 0 0 + p*p*X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complementaryChannel, traceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, U_apply, sp, sq] <;> ring

def N : Fin 3 → Matrix (Fin 2) (Fin 3) ℂ :=
  ![!![0, 1, 0; r, 0, 0], !![r, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 0, 1]]

lemma N_family : ∑ k, (N k)ᴴ * N k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply, sr] <;>
    simp only [hr']; ring_nf; simp only [hs2, hs3, hs4, hs5, hs6]; ring_nf

lemma N_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply N (receiverChannel (clonerDilation 1 2) X) =
      complementaryChannel (clonerDilation 1 2) X := by
  rw [rec_eq, comp_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [krausApply, N, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply, sr,
      Matrix.vecMul, dotProduct]
  all_goals (simp only [hp', hr']; ring_nf; simp only [hs2, hs3, hs4, hs5, hs6, hq2, hq3, hq4]; ring_nf)

def T : Fin 2 → Matrix (Fin 2) (Fin 3) ℂ :=
  ![!![1, 0, 0; 0, r, 0], !![0, r, 0; 0, 0, 1]]

def M' : Fin 2 ⊕ (Fin 2 × Fin 3) → Matrix (Fin 2) (Fin 3) ℂ
  | Sum.inl k => r • T k
  | Sum.inr ij => (1/2 : ℂ) • Matrix.single ij.1 ij.2 1

lemma M'_family : ∑ k, (M' k)ᴴ * M' k = 1 := by
  ext i j
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  fin_cases i <;> fin_cases j <;>
    simp [M', T, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply, sr,
      Matrix.single_apply]
  all_goals (simp only [hp', hr']; ring_nf; simp only [hs2, hs3, hs4, hs5, hs6, hq2, hq3, hq4]; ring_nf)

lemma M'_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply M' (receiverChannel (clonerDilation 1 2) X) =
      (complementaryChannel (clonerDilation 1 2) X)ᵀ := by
  rw [rec_eq, comp_eq]
  ext i j
  simp only [krausApply, Matrix.sum_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  fin_cases i <;> fin_cases j <;>
    simp [M', T, Fin.sum_univ_succ, Matrix.mul_apply, Matrix.conjTranspose_apply, sr,
      Matrix.single_apply]
  all_goals (simp only [hp', hr']; ring_nf; simp only [hs2, hs3, hs4, hs5, hs6, hq2, hq3, hq4]; ring_nf)

lemma main : IsDegradable (clonerDilation 1 2) ∧ ConjugateDegradable (clonerDilation 1 2) := by
  refine ⟨⟨iso, krausApply N, ?_, fun X => (N_eq X).symm⟩, iso, krausApply M', ?_, M'_eq⟩
  · convert X7S1.chan_of_kraus N N_family
  · convert X7S1.chan_of_kraus M' M'_family

end X7C12

end QAlgorithms.Papers.Independent.Support50.P01

end

section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01
  QAlgorithms.Papers.Independent.Information100.P67 in
theorem solution :
    IsDegradable (clonerDilation 1 2) ∧ ConjugateDegradable (clonerDilation 1 2) :=
  QAlgorithms.Papers.Independent.Support50.P01.X7C12.main

end
