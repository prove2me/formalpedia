-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.learning_replicas
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:59:49.443016+00:00
-- url     : https://prove2.me/submissions/b3e9fe11-c8ab-49cb-82f1-e1d962bdb222

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MeasureTheory
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

def X7R_sg (s : Fin 2) : ℂ := if s = 0 then 1 else -1
def X7R_N (d : ℕ) (s : Fin 2) : ℝ := Real.sqrt (2 * ((d : ℝ) + if s = 0 then 1 else -1))
def X7R_T {d : ℕ} (B : Op (ABC d)) (E : Op (Fin d)) : Op (AB d) :=
  fun x y => ∑ c, ∑ e, B (y, c) (x, e) * E e c

lemma X7R_sg_sq (s : Fin 2) : X7R_sg s * X7R_sg s = 1 := by
  unfold X7R_sg; split_ifs <;> norm_num

lemma X7R_alpha_apply (d : ℕ) (s : Fin 2) (a b c m : Fin d) :
    alphaEmbedding d s ((a, b), c) m = ((X7R_N d s)⁻¹ : ℂ) *
      ((if a = c ∧ b = m then 1 else 0) + X7R_sg s * (if a = m ∧ b = c then 1 else 0)) := by
  unfold alphaEmbedding X7R_N X7R_sg
  split_ifs <;> push_cast <;> ring

lemma X7R_P_apply (d : ℕ) (s : Fin 2) (x y : AB d) :
    pairProjector d s x y = (1/2 : ℂ) * ((if x.1 = y.1 ∧ x.2 = y.2 then 1 else 0) +
      X7R_sg s * (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)) := by
  unfold pairProjector X7R_sg
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq]

lemma X7R_P_symm (d : ℕ) (s : Fin 2) (x y : AB d) :
    pairProjector d s x y = pairProjector d s y x := by
  unfold pairProjector
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  congr 2
  · exact if_congr (by simp only [Prod.mk.injEq]; tauto) rfl rfl
  · congr 1; exact if_congr (by simp only [Prod.mk.injEq]; tauto) rfl rfl

lemma X7R_T_alpha_apply (d : ℕ) (s t : Fin 2) (E : Op (Fin d)) (r s' p q : Fin d) :
    X7R_T (alphaEmbedding d s * (alphaEmbedding d t)ᴴ) E (r, s') (p, q) =
      ((X7R_N d s)⁻¹ : ℂ) * ((X7R_N d t)⁻¹ : ℂ) *
      ((if q = s' then E r p else 0) + X7R_sg t * (if q = r then E s' p else 0) +
       X7R_sg s * (if p = s' then E r q else 0) +
       X7R_sg s * X7R_sg t * (if p = r then E s' q else 0)) := by
  simp only [X7R_T, Matrix.mul_apply, Matrix.conjTranspose_apply, X7R_alpha_apply]
  have hs : star (X7R_sg t) = X7R_sg t := by unfold X7R_sg; split_ifs <;> simp
  simp only [star_mul', star_add, hs, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_add, add_mul, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, one_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs <;> ring

lemma X7R_PKP_apply (d : ℕ) (a b : Fin 2) (E : Op (Fin d)) (r s' p q : Fin d) :
    (pairProjector d a * Matrix.kronecker E 1 * pairProjector d b : Op (AB d)) (r, s') (p, q) =
      (1/4 : ℂ) * ((if q = s' then E r p else 0) + X7R_sg a * (if q = r then E s' p else 0) +
       X7R_sg b * (if p = s' then E r q else 0) +
       X7R_sg b * X7R_sg a * (if p = r then E s' q else 0)) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, X7R_P_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mul_sum, Finset.sum_mul]
  split_ifs <;> subst_vars <;> simp_all <;> ring

lemma X7R_T_alpha (d : ℕ) (s t : Fin 2) (E : Op (Fin d)) :
    X7R_T (alphaEmbedding d s * (alphaEmbedding d t)ᴴ) E =
      ((4 * (X7R_N d s)⁻¹ * (X7R_N d t)⁻¹ : ℝ) : ℂ) •
        (pairProjector d t * Matrix.kronecker E 1 * pairProjector d s) := by
  ext ⟨r, s'⟩ ⟨p, q⟩
  rw [X7R_T_alpha_apply, Matrix.smul_apply, X7R_PKP_apply, smul_eq_mul]
  push_cast
  ring

lemma X7R_PP (d : ℕ) (s : Fin 2) :
    pairProjector d s * pairProjector d s = pairProjector d s := by
  ext ⟨r, s'⟩ ⟨p, q⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, X7R_P_apply]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mul_sum, Finset.sum_mul]
  fin_cases s <;> simp only [X7R_sg] <;> split_ifs <;> subst_vars <;> simp_all <;> norm_num

lemma X7R_T_add (d : ℕ) (B B' : Op (ABC d)) (E : Op (Fin d)) :
    X7R_T (B + B') E = X7R_T B E + X7R_T B' E := by
  ext x y; simp [X7R_T, add_mul, Finset.sum_add_distrib]

lemma X7R_T_sub (d : ℕ) (B B' : Op (ABC d)) (E : Op (Fin d)) :
    X7R_T (B - B') E = X7R_T B E - X7R_T B' E := by
  ext x y; simp [X7R_T, sub_mul, Finset.sum_sub_distrib]

lemma X7R_T_smul (d : ℕ) (c : ℂ) (B : Op (ABC d)) (E : Op (Fin d)) :
    X7R_T (c • B) E = c • X7R_T B E := by
  ext x y; simp [X7R_T, mul_assoc, Finset.mul_sum]

lemma X7R_T_zero (d : ℕ) (E : Op (Fin d)) : X7R_T (0 : Op (ABC d)) E = 0 := by
  ext x y; simp [X7R_T]

lemma X7R_T_sum (d : ℕ) {ι : Type*} (S : Finset ι) (B : ι → Op (ABC d)) (E : Op (Fin d)) :
    X7R_T (∑ i ∈ S, B i) E = ∑ i ∈ S, X7R_T (B i) E := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [X7R_T_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, X7R_T_add, ih]

lemma X7R_T_kron (d : ℕ) (s : Fin 2) (E : Op (Fin d)) :
    X7R_T (Matrix.kronecker (pairProjector d s) 1) E = Matrix.trace E • pairProjector d s := by
  ext ⟨r, s'⟩ ⟨p, q⟩
  simp only [X7R_T, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, X7R_P_symm]


lemma X7R_replica_lift (d : ℕ) (B : DiagonalInstrument d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    replica (liftDiagonal B) U i j = ∑ k, X7R_T (B i j k) (measurementEffect U k) := by
  ext x y
  simp only [replica, liftDiagonal, Matrix.sum_apply, X7R_T, measurementEffect,
    eq_self_iff_true, if_true, ↓reduceIte]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun e _ => ?_
  ring

lemma X7R_sum_eff (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ k, measurementEffect U k = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp U.2
  ext a b
  rw [Matrix.sum_apply]
  have := congrFun (congrFun h a) b
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def] at this
  simpa [measurementEffect] using this

lemma X7R_tr_eff (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    Matrix.trace (measurementEffect U k) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp U.2
  have := congrFun (congrFun h k) k
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Matrix.one_apply_eq] at this
  rw [← this]
  simp only [Matrix.trace, Matrix.diag, measurementEffect]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma X7R_K_sum (d : ℕ) (E : Fin d → Op (Fin d)) :
    ∑ k, Matrix.kronecker (E k) (1 : Op (Fin d)) = Matrix.kronecker (∑ k, E k) 1 := by
  ext x y
  simp [Matrix.sum_apply, Finset.sum_mul]

lemma X7R_sumPKP (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (a b : Fin 2) :
    ∑ k, pairProjector d a * Matrix.kronecker (measurementEffect U k) 1 * pairProjector d b =
      pairProjector d a * pairProjector d b := by
  have hK : Matrix.kronecker (1 : Op (Fin d)) (1 : Op (Fin d)) = 1 := Matrix.one_kronecker_one
  rw [← Finset.sum_mul, ← Finset.mul_sum, X7R_K_sum, X7R_sum_eff, hK, mul_one]

lemma X7R_sum_ite {M : Type*} [AddCommGroup M] {n : ℕ} (i : Fin n) (A : M) (f : Fin n → M) :
    ∑ k, (if k = i then A else f k) = ∑ k, f k + (A - f i) := by
  have : ∀ k, (if k = i then A else f k) = f k + if k = i then A - f i else 0 := by
    intro k; split_ifs with h
    · subst h; abel
    · simp
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma X7R_sum_ite2 {M : Type*} [AddCommGroup M] {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : M)
    (f : Fin n → M) :
    ∑ k, (if k = i then A else if k = j then B else f k) = ∑ k, f k + (A - f i) + (B - f j) := by
  rw [X7R_sum_ite i A (fun k => if k = j then B else f k), X7R_sum_ite j B f]
  simp only [if_neg hij]
  abel

lemma X7R_eq_of_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  (pow_left_inj₀ hx hy two_ne_zero).1 h

lemma X7R_N_sq (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) :
    X7R_N d s ^ 2 = 2 * ((d : ℝ) + if s = 0 then 1 else -1) := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold X7R_N
  rw [Real.sq_sqrt]
  split_ifs <;> linarith

lemma X7R_N_pos (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) : 0 < X7R_N d s := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold X7R_N
  apply Real.sqrt_pos.2
  split_ifs <;> linarith

lemma X7R_T_aa (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) (E : Op (Fin d)) :
    X7R_T (alphaEmbedding d s * (alphaEmbedding d s)ᴴ) E =
      ((2 / ((d : ℝ) + if s = 0 then 1 else -1) : ℝ) : ℂ) •
        (pairProjector d s * Matrix.kronecker E 1 * pairProjector d s) := by
  rw [X7R_T_alpha]
  congr 2
  have h1 := X7R_N_sq d hd s
  have h2 := X7R_N_pos d hd s
  have h3 : ((d : ℝ) + if s = 0 then 1 else -1) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    split_ifs <;> intro h <;> linarith
  field_simp
  rw [h1]; ring

lemma X7R_T_res (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) (E : Op (Fin d)) :
    X7R_T (residualProjector d s) E = Matrix.trace E • pairProjector d s -
      ((2 / ((d : ℝ) + if s = 0 then 1 else -1) : ℝ) : ℂ) •
        (pairProjector d s * Matrix.kronecker E 1 * pairProjector d s) := by
  unfold residualProjector
  rw [X7R_T_sub, X7R_T_kron, X7R_T_aa d hd]

lemma X7R_BO0 (d : ℕ) (a : ℝ) : blockOperator d (learningBlocks d a) 0 =
    ((1/(d : ℝ) - 2*a : ℝ) : ℂ) • (alphaEmbedding d 0 * (alphaEmbedding d 0)ᴴ) := by
  simp [blockOperator, learningBlocks, Fin.sum_univ_two, coordinateProjector]

lemma X7R_BO1 (d : ℕ) (a : ℝ) : blockOperator d (learningBlocks d a) 1 =
    ((1/(d : ℝ) : ℝ) : ℂ) • residualProjector d 0 := by
  simp [blockOperator, learningBlocks, Fin.sum_univ_two, coordinateProjector]

lemma X7R_BO4 (d : ℕ) (hd : d ≠ 2) (a : ℝ) : blockOperator d (learningBlocks d a) 4 =
    ((1/(d : ℝ) : ℝ) : ℂ) • residualProjector d 1 := by
  simp [blockOperator, learningBlocks, Fin.sum_univ_two, coordinateProjector, hd]

def X7R_v (d : ℕ) : ℂ := ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma X7R_BO2 (d : ℕ) (a : ℝ) : blockOperator d (learningBlocks d a) 2 =
    (((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ)) •
      (alphaEmbedding d 0 * (alphaEmbedding d 0)ᴴ) +
    (((Real.sqrt a : ℝ) : ℂ) * X7R_v d) • (alphaEmbedding d 0 * (alphaEmbedding d 1)ᴴ) +
    (X7R_v d * ((Real.sqrt a : ℝ) : ℂ)) • (alphaEmbedding d 1 * (alphaEmbedding d 0)ᴴ) +
    (X7R_v d * X7R_v d) • (alphaEmbedding d 1 * (alphaEmbedding d 1)ᴴ) := by
  simp [blockOperator, learningBlocks, Fin.sum_univ_two, coordinateProjector, X7R_v] <;> abel

lemma X7R_BO3 (d : ℕ) (a : ℝ) : blockOperator d (learningBlocks d a) 3 =
    (((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ)) •
      (alphaEmbedding d 0 * (alphaEmbedding d 0)ᴴ) -
    (((Real.sqrt a : ℝ) : ℂ) * X7R_v d) • (alphaEmbedding d 0 * (alphaEmbedding d 1)ᴴ) -
    (X7R_v d * ((Real.sqrt a : ℝ) : ℂ)) • (alphaEmbedding d 1 * (alphaEmbedding d 0)ᴴ) +
    (X7R_v d * X7R_v d) • (alphaEmbedding d 1 * (alphaEmbedding d 1)ᴴ) := by
  simp [blockOperator, learningBlocks, Fin.sum_univ_two, coordinateProjector, X7R_v] <;> abel

def X7R_q (d : ℕ) : ℝ := (Real.sqrt (9*(d : ℝ)*((d : ℝ)-1)))⁻¹

lemma X7R_q_sq (d : ℕ) (hd : 3 ≤ d) : X7R_q d ^ 2 = 1 / (9*(d : ℝ)*((d : ℝ)-1)) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold X7R_q
  rw [inv_pow, Real.sq_sqrt (by nlinarith), one_div]

lemma X7R_q_nonneg (d : ℕ) : 0 ≤ X7R_q d := by unfold X7R_q; positivity

lemma X7R_W0 (d : ℕ) (hd : 3 ≤ d) :
    Real.sqrt (learningParameter d) = X7R_q d * X7R_N d 0 / 2 := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hN := (X7R_N_pos d (by omega) 0).le
  apply X7R_eq_of_sq (Real.sqrt_nonneg _) (by have := X7R_q_nonneg d; positivity)
  rw [Real.sq_sqrt, div_pow, mul_pow, X7R_q_sq d hd, X7R_N_sq d (by omega)]
  · have h1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
    have h2 : (d : ℝ) ≠ 0 := by intro h; linarith
    have h4 : (d : ℝ) + 1 ≠ 0 := by intro h; linarith
    simp only [learningParameter, eq_self_iff_true, if_true, ↓reduceIte]
    field_simp
    ring
  · unfold learningParameter
    apply div_nonneg <;> nlinarith

lemma X7R_V1 (d : ℕ) (hd : 3 ≤ d) :
    (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = 3 * X7R_q d * X7R_N d 1 / 2 := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hN := (X7R_N_pos d (by omega) 1).le
  apply X7R_eq_of_sq (by positivity) (by have := X7R_q_nonneg d; positivity)
  rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num),
    div_pow, mul_pow, mul_pow, X7R_q_sq d hd, X7R_N_sq d (by omega)]
  have h1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (d : ℝ) ≠ 0 := by intro h; linarith
  simp only [show (1 : Fin 2) ≠ 0 from by decide, if_false]
  field_simp
  ring

lemma X7R_W0C (d : ℕ) (hd : 3 ≤ d) :
    ((Real.sqrt (learningParameter d) : ℝ) : ℂ) = (X7R_q d : ℂ) * (X7R_N d 0 : ℂ) / 2 := by
  rw [X7R_W0 d hd]; push_cast; ring

lemma X7R_V1C (d : ℕ) (hd : 3 ≤ d) :
    X7R_v d = 3 * (X7R_q d : ℂ) * (X7R_N d 1 : ℂ) / 2 := by
  have := congrArg (fun x : ℝ => (x : ℂ)) (X7R_V1 d hd)
  push_cast at this
  rw [X7R_v, this]

lemma X7R_filter (d : ℕ) (s : Fin 2) : learningReplicaFilter d s =
    (X7R_q d : ℂ) • (pairProjector d 0 + (if s = 0 then 3 else -3 : ℂ) • pairProjector d 1) := by
  unfold learningReplicaFilter X7R_q
  first | rfl | (simp only [Complex.ofReal_inv]) | (push_cast; rfl)

lemma X7R_TB0 (d : ℕ) (hd : 2 ≤ d) (a : ℝ) (E : Op (Fin d)) :
    X7R_T (blockOperator d (learningBlocks d a) 0) E =
      ((1/(d : ℂ) - 2 * (a : ℂ)) * (2 / ((d : ℂ) + 1))) •
        (pairProjector d 0 * Matrix.kronecker E 1 * pairProjector d 0) := by
  rw [X7R_BO0, X7R_T_smul, X7R_T_aa d hd, smul_smul]
  congr 1
  simp only [if_pos rfl]
  push_cast
  ring

lemma X7R_TB1 (d : ℕ) (hd : 2 ≤ d) (a : ℝ) (E : Op (Fin d)) :
    X7R_T (blockOperator d (learningBlocks d a) 1) E =
      (1/(d : ℂ)) • (Matrix.trace E • pairProjector d 0 - (2 / ((d : ℂ) + 1)) •
        (pairProjector d 0 * Matrix.kronecker E 1 * pairProjector d 0)) := by
  rw [X7R_BO1, X7R_T_smul, X7R_T_res d hd]
  simp only [if_pos rfl]
  push_cast
  rfl

lemma X7R_TB4 (d : ℕ) (hd : 3 ≤ d) (a : ℝ) (E : Op (Fin d)) :
    X7R_T (blockOperator d (learningBlocks d a) 4) E =
      (1/(d : ℂ)) • (Matrix.trace E • pairProjector d 1 - (2 / ((d : ℂ) - 1)) •
        (pairProjector d 1 * Matrix.kronecker E 1 * pairProjector d 1)) := by
  rw [X7R_BO4 d (by omega), X7R_T_smul, X7R_T_res d (by omega)]
  simp only [show (1 : Fin 2) ≠ 0 from by decide, if_false]
  push_cast
  ring_nf

lemma X7R_TB2 (d : ℕ) (hd : 3 ≤ d) (E : Op (Fin d)) :
    X7R_T (blockOperator d (learningBlocks d (learningParameter d)) 2) E =
      learningReplicaFilter d 0 * Matrix.kronecker E 1 * learningReplicaFilter d 0 := by
  have hN0 : (X7R_N d 0 : ℂ) ≠ 0 := by exact_mod_cast (X7R_N_pos d (by omega) 0).ne'
  have hN1 : (X7R_N d 1 : ℂ) ≠ 0 := by exact_mod_cast (X7R_N_pos d (by omega) 1).ne'
  rw [X7R_BO2]
  simp only [X7R_T_add, X7R_T_smul, X7R_T_alpha, X7R_filter, if_pos rfl]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add, smul_smul]
  rw [X7R_W0C d hd, X7R_V1C d hd]
  push_cast
  match_scalars <;> field_simp <;> ring

lemma X7R_TB3 (d : ℕ) (hd : 3 ≤ d) (E : Op (Fin d)) :
    X7R_T (blockOperator d (learningBlocks d (learningParameter d)) 3) E =
      learningReplicaFilter d 1 * Matrix.kronecker E 1 * learningReplicaFilter d 1 := by
  have hN0 : (X7R_N d 0 : ℂ) ≠ 0 := by exact_mod_cast (X7R_N_pos d (by omega) 0).ne'
  have hN1 : (X7R_N d 1 : ℂ) ≠ 0 := by exact_mod_cast (X7R_N_pos d (by omega) 1).ne'
  rw [X7R_BO3]
  simp only [X7R_T_add, X7R_T_sub, X7R_T_smul, X7R_T_alpha, X7R_filter,
    show (1 : Fin 2) ≠ 0 from by decide, if_false]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add, smul_smul]
  rw [X7R_W0C d hd, X7R_V1C d hd]
  push_cast
  match_scalars <;> field_simp <;> ring


lemma X7R_sumlin (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (s : Fin 2) (c1 c2 c3 : ℂ) :
    ∑ k, c1 • (c2 • ((1 : ℂ) • pairProjector d s - c3 •
      (pairProjector d s * Matrix.kronecker (measurementEffect U k) 1 * pairProjector d s))) =
    c1 • (c2 • ((d : ℂ) • pairProjector d s - c3 • pairProjector d s)) := by
  have hA : ∑ k, (pairProjector d s * Matrix.kronecker (measurementEffect U k) 1 *
      pairProjector d s) = pairProjector d s := by rw [X7R_sumPKP, X7R_PP]
  have hB : ∑ _k : Fin d, (1 : ℂ) • pairProjector d s = (d : ℂ) • pairProjector d s := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, Nat.cast_smul_eq_nsmul]
  rw [← Finset.smul_sum, ← Finset.smul_sum, Finset.sum_sub_distrib, hB, ← Finset.smul_sum, hA]

lemma X7R_rep_diag (d : ℕ) (hd : 3 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    replica (expandBlocks d (learningBlocks d (learningParameter d))) U i i =
      learningReplicaFormula U i i := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold expandBlocks
  rw [X7R_replica_lift]
  have hk : ∀ k, X7R_T (((classWeight d (outcomeClass i i k) : ℂ)⁻¹) •
      blockOperator d (learningBlocks d (learningParameter d)) (outcomeClass i i k))
      (measurementEffect U k) =
      if k = i then ((classWeight d 0 : ℂ)⁻¹) •
        (((1/(d : ℂ) - 2 * (learningParameter d : ℂ)) * (2 / ((d : ℂ) + 1))) •
        (pairProjector d 0 * Matrix.kronecker (measurementEffect U i) 1 * pairProjector d 0))
      else ((classWeight d 1 : ℂ)⁻¹) • ((1/(d : ℂ)) • ((1 : ℂ) • pairProjector d 0 -
        (2 / ((d : ℂ) + 1)) •
        (pairProjector d 0 * Matrix.kronecker (measurementEffect U k) 1 * pairProjector d 0))) := by
    intro k
    by_cases h : k = i
    · subst h
      have hc : outcomeClass k k k = 0 := by simp [outcomeClass]
      rw [if_pos rfl, hc, X7R_T_smul, X7R_TB0 d (by omega)]
    · have hc : outcomeClass i i k = 1 := by simp [outcomeClass, Ne.symm h]
      rw [if_neg h, hc, X7R_T_smul, X7R_TB1 d (by omega), X7R_tr_eff]
  simp only [Finset.sum_congr rfl fun k _ => hk k]
  rw [X7R_sum_ite, X7R_sumlin]
  simp only [learningReplicaFormula, if_pos rfl]
  have h1 : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (1 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h2 : (d : ℂ) ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (0 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h4 : (d : ℂ) + 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (-1 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h6 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) ^ 2 = ((1 : ℝ) : ℂ) := by push_cast; linear_combination h
    norm_cast at this; nlinarith
  have h6' : -1 + (d : ℂ) ^ 2 ≠ 0 := by rw [neg_add_eq_sub]; exact h6
  simp only [classWeight, learningParameter]
  push_cast
  try simp only [show (1 : Fin 5) ≠ 0 from by decide, show (1 : Fin 5) ≠ 4 from by decide,
    eq_self_iff_true, if_true, if_false, ↓reduceIte]
  match_scalars <;> field_simp <;> ring

lemma X7R_rep_off (d : ℕ) (hd : 3 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d)
    (hij : i ≠ j) :
    replica (expandBlocks d (learningBlocks d (learningParameter d))) U i j =
      learningReplicaFormula U i j := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold expandBlocks
  rw [X7R_replica_lift]
  have hk : ∀ k, X7R_T (((classWeight d (outcomeClass i j k) : ℂ)⁻¹) •
      blockOperator d (learningBlocks d (learningParameter d)) (outcomeClass i j k))
      (measurementEffect U k) =
      if k = i then ((classWeight d 2 : ℂ)⁻¹) •
        (learningReplicaFilter d 0 * Matrix.kronecker (measurementEffect U i) 1 *
          learningReplicaFilter d 0)
      else if k = j then ((classWeight d 3 : ℂ)⁻¹) •
        (learningReplicaFilter d 1 * Matrix.kronecker (measurementEffect U j) 1 *
          learningReplicaFilter d 1)
      else ((classWeight d 4 : ℂ)⁻¹) • ((1/(d : ℂ)) • ((1 : ℂ) • pairProjector d 1 -
        (2 / ((d : ℂ) - 1)) •
        (pairProjector d 1 * Matrix.kronecker (measurementEffect U k) 1 * pairProjector d 1))) := by
    intro k
    by_cases h : k = i
    · subst h
      have hc : outcomeClass k j k = 2 := by simp [outcomeClass, hij]
      rw [if_pos rfl, hc, X7R_T_smul, X7R_TB2 d hd]
    · by_cases h' : k = j
      · subst h'
        have hc : outcomeClass i k k = 3 := by simp [outcomeClass, hij, Ne.symm h]
        rw [if_neg h, if_pos rfl, hc, X7R_T_smul, X7R_TB3 d hd]
      · have hc : outcomeClass i j k = 4 := by simp [outcomeClass, hij, Ne.symm h, Ne.symm h']
        rw [if_neg h, if_neg h', hc, X7R_T_smul, X7R_TB4 d hd, X7R_tr_eff]
  simp only [Finset.sum_congr rfl fun k _ => hk k]
  rw [X7R_sum_ite2 i j hij, X7R_sumlin]
  simp only [learningReplicaFormula, if_neg hij]
  have h1 : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (1 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h2 : (d : ℂ) ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (0 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h5 : (d : ℂ) - 2 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (2 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  simp only [mul_add, add_mul]
  simp only [classWeight]
  push_cast
  try simp only [show (2 : Fin 5) ≠ 0 from by decide, show (2 : Fin 5) ≠ 4 from by decide,
    show (3 : Fin 5) ≠ 0 from by decide, show (3 : Fin 5) ≠ 4 from by decide,
    show (4 : Fin 5) ≠ 0 from by decide,
    eq_self_iff_true, if_true, if_false, ↓reduceIte]
  match_scalars <;> field_simp <;> ring


def X7R_J (d : ℕ) (k : Fin d) : Matrix (ABCD d) (ABC d) ℂ :=
  fun x y => if x.1 = y ∧ x.2 = k then 1 else 0

lemma X7R_lift_eq (d : ℕ) (B : DiagonalInstrument d) (i j : Fin d) :
    liftDiagonal B i j = ∑ k, X7R_J d k * B i j k * (X7R_J d k)ᴴ := by
  ext x y
  simp only [liftDiagonal, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, X7R_J]
  simp only [apply_ite star, star_one, star_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    one_mul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs <;> simp_all

lemma X7R_lift_psd (d : ℕ) (B : DiagonalInstrument d) (i j : Fin d)
    (h : ∀ k, (B i j k).PosSemidef) : (liftDiagonal B i j).PosSemidef := by
  rw [X7R_lift_eq]
  exact Matrix.posSemidef_sum _ fun k _ => (h k).mul_mul_conjTranspose_same _

lemma X7R_psd_rsmul {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ((r : ℂ) • M).PosSemidef :=
  hM.smul (Complex.zero_le_real.mpr hr)

lemma X7R_sg_star (s : Fin 2) : star (X7R_sg s) = X7R_sg s := by
  unfold X7R_sg; split_ifs <;> simp

lemma X7R_alpha_orth (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) :
    (alphaEmbedding d s)ᴴ * alphaEmbedding d s = 1 := by
  have hN := X7R_N_sq d hd s
  have hNp := (X7R_N_pos d hd s).ne'
  have hNc' : ((X7R_N d s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNp
  ext m m'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, X7R_alpha_apply,
    Matrix.one_apply]
  simp only [star_mul', star_add, X7R_sg_star, star_inv₀, Complex.star_def, Complex.conj_ofReal,
    apply_ite (starRingEnd ℂ), map_one, map_zero]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  fin_cases s <;> simp only [X7R_sg] at * <;> split_ifs <;> subst_vars <;> simp_all <;>
    field_simp <;> (have := congrArg (fun x : ℝ => (x : ℂ)) hN; push_cast at this) <;>
    linear_combination (-1 : ℂ) * this


lemma X7R_Palpha (d : ℕ) (s : Fin 2) :
    Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) * alphaEmbedding d s =
      alphaEmbedding d s := by
  ext ⟨⟨a, b⟩, c⟩ m
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, X7R_P_apply, X7R_alpha_apply]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  fin_cases s <;> simp only [X7R_sg] <;> split_ifs <;> subst_vars <;> simp_all <;> ring

lemma X7R_P_herm (d : ℕ) (s : Fin 2) : (pairProjector d s)ᴴ = pairProjector d s := by
  ext x y
  rw [Matrix.conjTranspose_apply, X7R_P_symm, X7R_P_apply]
  simp only [star_mul', star_add, X7R_sg_star, apply_ite star, star_one, star_zero]
  norm_num

lemma X7R_KP_herm (d : ℕ) (s : Fin 2) :
    (Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)))ᴴ =
      Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, X7R_P_herm, Matrix.conjTranspose_one]

lemma X7R_KP_idem (d : ℕ) (s : Fin 2) :
    Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) *
      Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) =
      Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) := by
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, X7R_PP, Matrix.one_mul]

lemma X7R_res_herm (d : ℕ) (s : Fin 2) :
    (residualProjector d s)ᴴ = residualProjector d s := by
  unfold residualProjector
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    X7R_KP_herm]

lemma X7R_res_idem (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) :
    residualProjector d s * residualProjector d s = residualProjector d s := by
  unfold residualProjector
  have h1 := X7R_KP_idem d s
  have h2 := X7R_Palpha d s
  have h3 : (alphaEmbedding d s)ᴴ * Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) =
      (alphaEmbedding d s)ᴴ := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, X7R_KP_herm] at this
  have h4 := X7R_alpha_orth d hd s
  have h2' : ∀ X : Matrix (Fin d) (ABC d) ℂ,
      Matrix.kronecker (pairProjector d s) (1 : Op (Fin d)) * (alphaEmbedding d s * X) =
        alphaEmbedding d s * X := by
    intro X; rw [← Matrix.mul_assoc, h2]
  have h4' : ∀ X : Matrix (Fin d) (ABC d) ℂ,
      (alphaEmbedding d s)ᴴ * (alphaEmbedding d s * X) = X := by
    intro X; rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  simp only [sub_mul, mul_sub, Matrix.mul_assoc, h1, h2', h3, h4']
  abel

lemma X7R_res_psd (d : ℕ) (hd : 2 ≤ d) (s : Fin 2) : (residualProjector d s).PosSemidef := by
  have : residualProjector d s = (residualProjector d s)ᴴ * residualProjector d s := by
    rw [X7R_res_herm, X7R_res_idem d hd]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma X7R_v_star (d : ℕ) : star (X7R_v d) = X7R_v d := by
  simp only [X7R_v, star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal]

lemma X7R_BO2_outer (d : ℕ) (a : ℝ) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    (((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ)) •
      (alphaEmbedding d 0 * (alphaEmbedding d 0)ᴴ) +
    (σ * (((Real.sqrt a : ℝ) : ℂ) * X7R_v d)) • (alphaEmbedding d 0 * (alphaEmbedding d 1)ᴴ) +
    (σ * (X7R_v d * ((Real.sqrt a : ℝ) : ℂ))) • (alphaEmbedding d 1 * (alphaEmbedding d 0)ᴴ) +
    (X7R_v d * X7R_v d) • (alphaEmbedding d 1 * (alphaEmbedding d 1)ᴴ) =
    (((Real.sqrt a : ℝ) : ℂ) • alphaEmbedding d 0 + (σ * X7R_v d) • alphaEmbedding d 1) *
      (((Real.sqrt a : ℝ) : ℂ) • alphaEmbedding d 0 + (σ * X7R_v d) • alphaEmbedding d 1)ᴴ := by
  rcases hσ with rfl | rfl <;>
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_mul', X7R_v_star,
    Complex.star_def, Complex.conj_ofReal, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul, map_one, map_neg] <;>
  module

lemma X7R_BO_psd (d : ℕ) (hd : 3 ≤ d) (l : Fin 5) :
    (blockOperator d (learningBlocks d (learningParameter d)) l).PosSemidef := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by fin_cases l <;> simp
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · rw [X7R_BO0]
    refine X7R_psd_rsmul _ ?_ (Matrix.posSemidef_self_mul_conjTranspose _)
    have h1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
    have h2 : (d : ℝ) ≠ 0 := by intro h; linarith
    have e : 1 / (d : ℝ) - 2 * learningParameter d =
        (8 * (d : ℝ) - 10) / (9 * (d : ℝ) * ((d : ℝ) - 1)) := by
      unfold learningParameter; field_simp; ring
    rw [e]
    apply div_nonneg
    · linarith
    · apply mul_nonneg (by positivity); linarith
  · rw [X7R_BO1]
    exact X7R_psd_rsmul _ (by positivity) (X7R_res_psd d (by omega) 0)
  · have := X7R_BO2_outer d (learningParameter d) 1 (Or.inl rfl)
    simp only [one_mul] at this
    rw [X7R_BO2, this]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · have := X7R_BO2_outer d (learningParameter d) (-1) (Or.inr rfl)
    rw [X7R_BO3]
    have e : ∀ (A B C D : Op (ABC d)) (x y z w : ℂ),
        x • A - y • B - z • C + w • D = x • A + (-1 * y) • B + (-1 * z) • C + w • D := by
      intros; module
    rw [e, this]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [X7R_BO4 d (by omega)]
    exact X7R_psd_rsmul _ (by positivity) (X7R_res_psd d (by omega) 1)

lemma X7R_R_psd (d : ℕ) (hd : 3 ≤ d) (i j : Fin d) :
    (expandBlocks d (learningBlocks d (learningParameter d)) i j).PosSemidef := by
  unfold expandBlocks
  apply X7R_lift_psd
  intro k
  have hw : 0 ≤ classWeight d (outcomeClass i j k) := by
    have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    unfold classWeight
    split_ifs <;> nlinarith
  have : ((classWeight d (outcomeClass i j k) : ℂ))⁻¹ =
      (((classWeight d (outcomeClass i j k))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact X7R_psd_rsmul _ (inv_nonneg.mpr hw) (X7R_BO_psd d hd _)


lemma X7R_count {M : Type*} [AddCommGroup M] [Module ℂ M] (d : ℕ) (k : Fin d) (F : Fin 5 → M) :
    ∑ i, ∑ j, F (outcomeClass i j k) =
      F 0 + ((d : ℂ) - 1) • (F 1 + F 2 + F 3) + (((d : ℂ) - 1) * ((d : ℂ) - 2)) • F 4 := by
  have hi : ∀ i, ∑ j, F (outcomeClass i j k) = if i = k then
      ((d : ℂ) • F 2 + (F 0 - F 2)) else ((d : ℂ) • F 4 + (F 1 - F 4) + (F 3 - F 4)) := by
    intro i
    by_cases h : i = k
    · subst h
      rw [if_pos rfl]
      have : ∀ j, F (outcomeClass i j i) = if j = i then F 0 else F 2 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [outcomeClass]
        · simp [outcomeClass, Ne.symm hj, hj]
      rw [Finset.sum_congr rfl fun j _ => this j, X7R_sum_ite, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    · rw [if_neg h]
      have : ∀ j, F (outcomeClass i j k) = if j = i then F 1 else if j = k then F 3 else F 4 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [outcomeClass, h]
        · by_cases hjk : j = k
          · subst hjk; simp [outcomeClass, Ne.symm hj, h, hj]
          · simp [outcomeClass, Ne.symm hj, h, Ne.symm hjk, hj, hjk]
      rw [Finset.sum_congr rfl fun j _ => this j, X7R_sum_ite2 i k h, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [Finset.sum_congr rfl fun i _ => hi i, X7R_sum_ite, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  module

lemma X7R_P01 (d : ℕ) : pairProjector d 0 + pairProjector d 1 = 1 := by
  ext x y
  rw [Matrix.add_apply, X7R_P_apply, X7R_P_apply, Matrix.one_apply]
  simp only [X7R_sg, if_pos rfl, show (1 : Fin 2) ≠ 0 from by decide, if_false]
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq]
  split_ifs <;> ring

lemma X7R_K01 (d : ℕ) : Matrix.kronecker (pairProjector d 0) (1 : Op (Fin d)) +
    Matrix.kronecker (pairProjector d 1) (1 : Op (Fin d)) = 1 := by
  simp only [Matrix.kronecker]
  rw [← Matrix.add_kronecker, X7R_P01, Matrix.one_kronecker_one]

lemma X7R_sumBO (d : ℕ) (hd : 3 ≤ d) :
    ∑ l : Fin 5, blockOperator d (learningBlocks d (learningParameter d)) l =
      (1 / (d : ℂ)) • (1 : Op (ABC d)) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Fin.sum_univ_five, X7R_BO0, X7R_BO1, X7R_BO2, X7R_BO3, X7R_BO4 d (by omega)]
  unfold residualProjector
  have hlp : 0 ≤ learningParameter d := by
    unfold learningParameter; apply div_nonneg (by linarith)
    apply mul_nonneg (by positivity); linarith
  have ha : ((Real.sqrt (learningParameter d) : ℝ) : ℂ) *
      ((Real.sqrt (learningParameter d) : ℝ) : ℂ) = (learningParameter d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hlp]
  have hv : X7R_v d * X7R_v d = 1 / (2 * (d : ℂ)) := by
    have e : X7R_v d = (((Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
      rw [X7R_v]; push_cast; rfl
    have e2 : ((Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt 2)⁻¹) * ((Real.sqrt (d : ℝ))⁻¹ *
        (Real.sqrt 2)⁻¹) = 1 / (2 * (d : ℝ)) := by
      have h1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ d by positivity)
      have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h4 : Real.sqrt (d : ℝ) ≠ 0 := by positivity
      have h5 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]; ring
    rw [e, ← Complex.ofReal_mul, e2]; push_cast; ring
  rw [ha, hv, ← X7R_K01]
  push_cast
  module

lemma X7R_total (d : ℕ) (hd : 3 ≤ d) :
    ∑ i, ∑ j, expandBlocks d (learningBlocks d (learningParameter d)) i j =
      learningTotal ((1 / (d : ℂ)) • (1 : Op (Fin d))) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (1 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h5 : (d : ℂ) - 2 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (2 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have hk : ∀ k : Fin d, ∑ i : Fin d, ∑ j : Fin d, (((classWeight d (outcomeClass i j k) : ℂ))⁻¹ •
      blockOperator d (learningBlocks d (learningParameter d)) (outcomeClass i j k)) =
      (1 / (d : ℂ)) • (1 : Op (ABC d)) := by
    intro k
    rw [X7R_count d k (fun l => ((classWeight d l : ℂ))⁻¹ •
      blockOperator d (learningBlocks d (learningParameter d)) l), ← X7R_sumBO d hd,
      Fin.sum_univ_five]
    simp only [classWeight]
    push_cast
    try simp only [show (2 : Fin 5) ≠ 0 from by decide, show (2 : Fin 5) ≠ 4 from by decide,
      show (3 : Fin 5) ≠ 0 from by decide, show (3 : Fin 5) ≠ 4 from by decide,
      show (4 : Fin 5) ≠ 0 from by decide, show (1 : Fin 5) ≠ 0 from by decide,
      show (1 : Fin 5) ≠ 4 from by decide, eq_self_iff_true, if_true, if_false, ↓reduceIte]
    match_scalars <;> field_simp <;> ring
  ext x y
  simp only [expandBlocks, liftDiagonal, Matrix.sum_apply]
  by_cases h : x.2 = y.2
  · simp only [if_pos h]
    have := congrFun (congrFun (hk x.2) x.1) y.1
    simp only [Matrix.sum_apply] at this
    rw [this]
    obtain ⟨⟨⟨a, b⟩, c⟩, k⟩ := x
    obtain ⟨⟨⟨a', b'⟩, c'⟩, k'⟩ := y
    simp only at h
    subst h
    simp only [learningTotal, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, and_true]
    split_ifs <;> simp_all
  · simp only [if_neg h, Finset.sum_const_zero, learningTotal]
    rw [if_neg (by tauto)]

lemma X7R_part1 (d : ℕ) (hd : 3 ≤ d) :
    IsReplicationStrategy .learning (expandBlocks d (learningBlocks d (learningParameter d))) := by
  refine ⟨fun i j => X7R_R_psd d hd i j, (1 / (d : ℂ)) • (1 : Op (Fin d)), ?_, ?_,
    X7R_total d hd⟩
  · have : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact X7R_psd_rsmul _ (by positivity) Matrix.PosSemidef.one
  · have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (d : ℂ) ≠ 0 := by
      intro h; have : ((d : ℝ) : ℂ) = (0 : ℝ) := by push_cast; linear_combination h
      have := Complex.ofReal_injective this; linarith
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp


def X7R_tv {d : ℕ} (u w : Fin d → ℂ) : AB d → ℂ := fun p => u p.1 * w p.2
def X7R_col {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) : Fin d → ℂ :=
  fun a => (U : Op (Fin d)) a i

lemma X7R_trace_kron (d : ℕ) (X : Op (AB d)) (U : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
    Matrix.trace (X * Matrix.kronecker (measurementEffect U i) (measurementEffect U j)) =
      star (X7R_tv (X7R_col U i) (X7R_col U j)) ⬝ᵥ
        (X *ᵥ X7R_tv (X7R_col U i) (X7R_col U j)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, X7R_tv, X7R_col, Matrix.kronecker, Matrix.kroneckerMap_apply,
    measurementEffect]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul', Complex.star_def]
  ring

lemma X7R_P_mulVec (d : ℕ) (s : Fin 2) (u w : Fin d → ℂ) :
    pairProjector d s *ᵥ X7R_tv u w = (1/2 : ℂ) • (X7R_tv u w + X7R_sg s • X7R_tv w u) := by
  ext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, X7R_P_apply, X7R_tv,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [mul_add, add_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  ring

lemma X7R_K_mulVec (d : ℕ) (E : Op (Fin d)) (u w : Fin d → ℂ) :
    Matrix.kronecker E (1 : Op (Fin d)) *ᵥ X7R_tv u w = X7R_tv (E *ᵥ u) w := by
  ext ⟨a, b⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, X7R_tv]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

lemma X7R_E_col (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (k m : Fin d) :
    measurementEffect U k *ᵥ X7R_col U m = if k = m then X7R_col U m else 0 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp U.2
  have := congrFun (congrFun h k) m
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, Matrix.one_apply] at this
  ext a
  simp only [Matrix.mulVec, dotProduct, measurementEffect, X7R_col]
  have e : ∑ b, (U : Op (Fin d)) a k * conj ((U : Op (Fin d)) b k) * (U : Op (Fin d)) b m =
      (U : Op (Fin d)) a k * ∑ b, conj ((U : Op (Fin d)) b k) * (U : Op (Fin d)) b m := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
  rw [e, this]
  split_ifs with hkm
  · subst hkm; simp [X7R_col]
  · simp

lemma X7R_K_col (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (k m : Fin d) (w : Fin d → ℂ) :
    Matrix.kronecker (measurementEffect U k) (1 : Op (Fin d)) *ᵥ X7R_tv (X7R_col U m) w =
      if k = m then X7R_tv (X7R_col U m) w else 0 := by
  rw [X7R_K_mulVec, X7R_E_col]
  split_ifs
  · rfl
  · ext p; simp [X7R_tv]

lemma X7R_tv_dot (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) (a b c e : Fin d) :
    star (X7R_tv (X7R_col U a) (X7R_col U b)) ⬝ᵥ X7R_tv (X7R_col U c) (X7R_col U e) =
      (if a = c then 1 else 0) * (if b = e then 1 else 0) := by
  have h := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h1 := congrFun (congrFun h a) c
  have h2 := congrFun (congrFun h b) e
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h1 h2
  rw [← h1, ← h2, Finset.sum_mul_sum]
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, X7R_tv, X7R_col, star_mul']
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma X7R_hq (d : ℕ) (hd : 3 ≤ d) :
    (X7R_q d : ℂ) * (X7R_q d : ℂ) = 1 / (9 * (d : ℂ) * ((d : ℂ) - 1)) := by
  have := X7R_q_sq d hd
  have e := congrArg (fun x : ℝ => (x : ℂ)) this
  push_cast at e
  rw [← e]; ring

lemma X7R_QXQ (d : ℕ) (hd : 3 ≤ d) (s : Fin 2) (X : Op (AB d)) :
    learningReplicaFilter d s * X * learningReplicaFilter d s =
      (1 / (9 * (d : ℂ) * ((d : ℂ) - 1))) •
        ((pairProjector d 0 + (if s = 0 then 3 else -3 : ℂ) • pairProjector d 1) * X *
          (pairProjector d 0 + (if s = 0 then 3 else -3 : ℂ) • pairProjector d 1)) := by
  rw [X7R_filter, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, X7R_hq d hd]

def X7R_D (d : ℕ) : ℝ :=
  (16*(d : ℝ)-2)/(9*(d : ℝ)*((d : ℝ)^2-1)) + ((d : ℝ)^2-3)/((d : ℝ)*((d : ℝ)^2-1))

def X7R_O (d : ℕ) : ℝ :=
  8 / (9 * (d : ℝ) * ((d : ℝ) - 1)^2) + 1 / ((d : ℝ) * ((d : ℝ) - 1)^2 * ((d : ℝ) - 2)) +
    ((d : ℝ) - 3) / (2 * ((d : ℝ) - 1)^2 * ((d : ℝ) - 2))

lemma X7R_tr_diag (d : ℕ) (hd : 3 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    Matrix.trace (learningReplicaFormula U i i *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U i)) = (X7R_D d : ℂ) := by
  simp only [learningReplicaFormula, eq_self_iff_true, if_true, ↓reduceIte]
  rw [X7R_trace_kron]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, X7R_P_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, X7R_K_col, eq_self_iff_true, if_true, ↓reduceIte, dotProduct_add,
    dotProduct_smul, X7R_tv_dot, smul_eq_mul, X7R_sg]
  simp only [X7R_D]
  push_cast
  ring

lemma X7R_tr_off (d : ℕ) (hd : 3 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d)
    (hij : i ≠ j) :
    Matrix.trace (learningReplicaFormula U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j)) = (X7R_O d : ℂ) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [learningReplicaFormula, if_neg hij]
  rw [X7R_QXQ d hd, X7R_QXQ d hd, X7R_trace_kron]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, X7R_P_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, X7R_K_col, eq_self_iff_true, if_true, ↓reduceIte, if_neg hij, if_neg (Ne.symm hij),
    Matrix.mulVec_zero, smul_zero, add_zero, zero_add, dotProduct_add, dotProduct_smul,
    dotProduct_zero, X7R_tv_dot, smul_eq_mul, X7R_sg, mul_one, mul_zero, zero_mul]
  have h1 : (d : ℂ) - 1 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (1 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h2 : (d : ℂ) ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (0 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  have h5 : (d : ℂ) - 2 ≠ 0 := by
    intro h; have : ((d : ℝ) : ℂ) = (2 : ℝ) := by push_cast; linear_combination h
    have := Complex.ofReal_injective this; linarith
  simp only [X7R_O]
  push_cast
  field_simp
  ring


lemma X7R_score_integrand (d : ℕ) (hd : 3 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    scoreIntegrand (expandBlocks d (learningBlocks d (learningParameter d))) U =
      (X7R_D d + ((d : ℝ) - 1) * X7R_O d) / (d : ℝ) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold scoreIntegrand
  have key : ∀ i j, (Matrix.trace (replica (expandBlocks d (learningBlocks d
      (learningParameter d))) U i j * Matrix.kronecker (measurementEffect U i)
        (measurementEffect U j))).re = if j = i then X7R_D d else X7R_O d := by
    intro i j
    by_cases h : j = i
    · subst h
      rw [X7R_rep_diag d hd, X7R_tr_diag d hd, if_pos rfl, Complex.ofReal_re]
    · rw [X7R_rep_off d hd U i j (Ne.symm h), X7R_tr_off d hd U i j (Ne.symm h), if_neg h,
        Complex.ofReal_re]
  simp only [key]
  rw [Finset.sum_congr rfl fun i _ => X7R_sum_ite i (X7R_D d) (fun _ => X7R_O d)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (d : ℝ) ≠ 0 := by intro h; linarith
  field_simp
  ring

lemma X7R_part2 (d : ℕ) (hd : 3 ≤ d) :
    haarReplicationScore (expandBlocks d (learningBlocks d (learningParameter d))) =
      learningValue d := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold haarReplicationScore
  simp only [X7R_score_integrand d hd]
  rw [integral_const]
  have hμ : (QAlgorithms.Schur.unitaryHaar d).real Set.univ = 1 := by
    rw [Measure.real, show QAlgorithms.Schur.unitaryHaar d Set.univ = 1 from
      Measure.haarMeasure_self]
    simp
  rw [hμ, one_smul]
  have hd2 : d ≠ 2 := by omega
  simp only [learningValue, hd2, if_false, X7R_D, X7R_O]
  have h1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (d : ℝ) ≠ 0 := by intro h; linarith
  have h4 : (d : ℝ) + 1 ≠ 0 := by intro h; linarith
  have h5 : (d : ℝ) - 2 ≠ 0 := by intro h; linarith
  have h6 : (d : ℝ) ^ 2 - 1 ≠ 0 := by intro h; nlinarith
  field_simp
  ring

end QAlgorithms.Papers.Independent.Claimed50.P17

end

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P17 in
theorem solution (d : ℕ) (hd : 3 ≤ d) :
    let R := expandBlocks d (learningBlocks d (learningParameter d))
    IsReplicationStrategy .learning R ∧ haarReplicationScore R = learningValue d ∧
    ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica R U i j = learningReplicaFormula U i j := by
  intro R
  refine ⟨X7R_part1 d hd, X7R_part2 d hd, fun U i j => ?_⟩
  by_cases h : i = j
  · subst h; exact X7R_rep_diag d hd U i
  · exact X7R_rep_off d hd U i j h

end
