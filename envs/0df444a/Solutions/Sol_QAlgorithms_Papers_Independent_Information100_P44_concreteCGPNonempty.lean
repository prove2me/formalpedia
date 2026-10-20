-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.concreteCGPNonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:08:42.288817+00:00
-- url     : https://prove2.me/submissions/436e5f34-0bd1-4f32-a463-298705992971

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44

attribute [local instance] Classical.propDecidable

/-- a = e^{-1} -/
def g53g_a : ℝ := Real.exp (-1)
def g53g_t01 : ℝ := (1/10) / (9/20 - 7/10 * g53g_a)
def g53g_t03 : ℝ := (1/20) / (1/5 - 7/20 * g53g_a ^ 3)

/-- coarse Gibbs-preserving stochastic matrix on levels (0, 1, 3) -/
def g53g_S : Fin 3 → Fin 3 → ℝ :=
  ![![1 - 2 * g53g_a * g53g_t01 - g53g_a ^ 3 * g53g_t03, g53g_t01, g53g_t03],
    ![2 * g53g_a * g53g_t01, 1 - g53g_t01, 0],
    ![g53g_a ^ 3 * g53g_t03, 0, 1 - g53g_t03]]

def g53g_L : Fin 4 → Fin 3 := ![0, 1, 1, 2]
def g53g_w : Fin 4 → ℝ := ![1, 1/2, 1/2, 1]

def g53g_T (x u : Fin 4) : ℝ := g53g_S (g53g_L x) (g53g_L u) * g53g_w x

lemma g53g_abnd : 0.367 < g53g_a ∧ g53g_a < 0.368 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have e : g53g_a = (Real.exp 1)⁻¹ := by rw [g53g_a, Real.exp_neg]
  rw [e]
  constructor
  · rw [lt_inv_comm₀ (by norm_num) (by positivity)]; linarith
  · rw [inv_lt_comm₀ (by positivity) (by norm_num)]; linarith

lemma g53g_d1 : 0 < 9/20 - 7/10 * g53g_a := by have := g53g_abnd; linarith
lemma g53g_a3 : 0 < g53g_a ^ 3 ∧ g53g_a ^ 3 < 0.05 := by
  obtain ⟨h1, h2⟩ := g53g_abnd
  constructor
  · positivity
  · nlinarith [pow_lt_pow_left₀ h2 (by linarith) (by norm_num : (3:ℕ) ≠ 0)]
lemma g53g_d3 : 0 < 1/5 - 7/20 * g53g_a ^ 3 := by have := g53g_a3; linarith

lemma g53g_t01_bnd : 0 ≤ g53g_t01 ∧ g53g_t01 ≤ 0.53 := by
  have hd := g53g_d1
  have := g53g_abnd
  unfold g53g_t01
  constructor
  · positivity
  · rw [div_le_iff₀ hd]; nlinarith
lemma g53g_t03_bnd : 0 ≤ g53g_t03 ∧ g53g_t03 ≤ 0.3 := by
  have hd := g53g_d3
  have := g53g_a3
  unfold g53g_t03
  constructor
  · positivity
  · rw [div_le_iff₀ hd]; nlinarith

lemma g53g_S_nonneg (i j : Fin 3) : 0 ≤ g53g_S i j := by
  obtain ⟨a1, a2⟩ := g53g_abnd
  obtain ⟨b1, b2⟩ := g53g_a3
  obtain ⟨c1, c2⟩ := g53g_t01_bnd
  obtain ⟨d1, d2⟩ := g53g_t03_bnd
  fin_cases i <;> fin_cases j <;> simp [g53g_S] <;> nlinarith [mul_nonneg (le_of_lt (by linarith : (0:ℝ) < g53g_a)) c1, mul_nonneg b1.le d1]

lemma g53g_T_nonneg (x u : Fin 4) : 0 ≤ g53g_T x u := by
  unfold g53g_T
  apply mul_nonneg (g53g_S_nonneg _ _)
  fin_cases x <;> simp [g53g_w] <;> norm_num

lemma g53g_colsum (u : Fin 4) : ∑ x, g53g_T x u = 1 := by
  simp only [Fin.sum_univ_four, g53g_T]
  fin_cases u <;> simp [g53g_S, g53g_L, g53g_w] <;> ring

/-- unnormalized Gibbs weights -/
def g53g_G : Fin 4 → ℝ := ![1, g53g_a, g53g_a, g53g_a ^ 3]

lemma g53g_gibbs (x : Fin 4) : ∑ u, g53g_T x u * g53g_G u = g53g_G x := by
  simp only [Fin.sum_univ_four, g53g_T]
  fin_cases x <;> simp [g53g_S, g53g_L, g53g_w, g53g_G] <;> ring

def g53g_F (p : Fin 4 × Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.single p.1 p.2 ((Real.sqrt (g53g_T p.1 p.2) : ℝ) : ℂ)

def g53g_E (k : Fin 16) : Matrix (Fin 4) (Fin 4) ℂ := g53g_F (finProdFinEquiv.symm k)

lemma g53g_sq (x u : Fin 4) :
    ((Real.sqrt (g53g_T x u) : ℝ) : ℂ) * star ((Real.sqrt (g53g_T x u) : ℝ) : ℂ) = (g53g_T x u : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (g53g_T_nonneg x u)]

lemma g53g_sq' (x u : Fin 4) :
    star ((Real.sqrt (g53g_T x u) : ℝ) : ℂ) * ((Real.sqrt (g53g_T x u) : ℝ) : ℂ) = (g53g_T x u : ℂ) := by
  rw [mul_comm, g53g_sq]

lemma g53g_sumE (f : Fin 4 × Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ k : Fin 16, f (finProdFinEquiv.symm k) = ∑ p, f p :=
  Equiv.sum_comp finProdFinEquiv.symm f

lemma g53g_kraus : IsKrausFamily g53g_E := by
  unfold IsKrausFamily g53g_E
  rw [g53g_sumE (fun p => (g53g_F p)ᴴ * g53g_F p)]
  have : ∀ p : Fin 4 × Fin 4, (g53g_F p)ᴴ * g53g_F p = Matrix.single p.2 p.2 ((g53g_T p.1 p.2 : ℂ)) := by
    intro p
    simp only [g53g_F, Matrix.conjTranspose_single, Matrix.single_mul_single_same, g53g_sq']
  simp only [this]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [and_self, true_and]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := g53g_colsum i
    simp [this, ← Complex.ofReal_sum]
  · simp only [h, if_false]
    apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun hh => h (hh.1.symm.trans hh.2))]

lemma g53g_apply (X : Matrix (Fin 4) (Fin 4) ℂ) :
    krausApply g53g_E X = Matrix.diagonal (fun x => ∑ u, (g53g_T x u : ℂ) * X u u) := by
  unfold krausApply g53g_E
  rw [g53g_sumE (fun p => g53g_F p * X * (g53g_F p)ᴴ)]
  have : ∀ p : Fin 4 × Fin 4, g53g_F p * X * (g53g_F p)ᴴ =
      Matrix.single p.1 p.1 ((g53g_T p.1 p.2 : ℂ) * X p.2 p.2) := by
    intro p
    simp only [g53g_F, Matrix.conjTranspose_single, Matrix.single_mul_mul_single]
    congr 1
    rw [mul_comm, ← mul_assoc, g53g_sq']
  simp only [this]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp only [h, if_false]
    apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun hh : x = i ∧ x = j => h (hh.1.symm.trans hh.2))]

lemma g53g_k1 : g53g_t01 * (9/20 - 7/10 * g53g_a) = 1/10 := by
  unfold g53g_t01; rw [div_mul_cancel₀ _ g53g_d1.ne']
lemma g53g_k2 : g53g_t03 * (1/5 - 7/20 * g53g_a ^ 3) = 1/20 := by
  unfold g53g_t03; rw [div_mul_cancel₀ _ g53g_d3.ne']

lemma g53g_expE (u : Fin 4) : Real.exp (-1 * fixedEnergy u) = g53g_G u := by
  fin_cases u <;> simp [fixedEnergy, g53g_G, g53g_a]
  rw [← Real.exp_nat_mul]; norm_num

lemma g53g_gw (x : Fin 4) :
    ∑ u, g53g_T x u * gibbsWeight fixedEnergy 1 u = gibbsWeight fixedEnergy 1 x := by
  simp only [gibbsWeight, g53g_expE, mul_div_assoc', ← Finset.sum_div, g53g_gibbs]

lemma g53g_pop (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X = fixedRho) :
    FixedPopulations (Matrix.diagonal (fun x => ∑ u, (g53g_T x u : ℂ) * X u u)) := by
  subst hX
  have r0 : g53g_T 0 0 * (35/100) + g53g_T 0 1 * (25/100) + g53g_T 0 2 * (20/100) +
      g53g_T 0 3 * (20/100) = 1/2 := by
    simp [g53g_T, g53g_S, g53g_L, g53g_w]; linear_combination g53g_k1 + g53g_k2
  have r1 : (g53g_T 1 0 + g53g_T 2 0) * (35/100) + (g53g_T 1 1 + g53g_T 2 1) * (25/100) +
      (g53g_T 1 2 + g53g_T 2 2) * (20/100) + (g53g_T 1 3 + g53g_T 2 3) * (20/100) = 7/20 := by
    simp [g53g_T, g53g_S, g53g_L, g53g_w]; linear_combination -g53g_k1
  have r3 : g53g_T 3 0 * (35/100) + g53g_T 3 1 * (25/100) + g53g_T 3 2 * (20/100) +
      g53g_T 3 3 * (20/100) = 3/20 := by
    simp [g53g_T, g53g_S, g53g_L, g53g_w]; linear_combination -g53g_k2
  have c0 := congrArg (fun r : ℝ => (r : ℂ)) r0
  have c1 := congrArg (fun r : ℝ => (r : ℂ)) r1
  have c3 := congrArg (fun r : ℝ => (r : ℂ)) r3
  push_cast at c0 c1 c3
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_four, fixedRho]
  · linear_combination c0
  · linear_combination c1
  · linear_combination c3

lemma g53g_choi : choi (krausApply g53g_E) = Matrix.diagonal (fun p => (g53g_T p.1 p.2 : ℂ)) := by
  ext p q
  simp only [choi, g53g_apply, Matrix.diagonal_apply, matrixUnit, Matrix.single_apply]
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  by_cases h1 : a = c
  · subst h1
    by_cases h2 : b = d
    · subst h2; simp
    · simp only [if_true]
      rw [if_neg (by simpa using h2)]
      apply Finset.sum_eq_zero; intro x _
      rw [if_neg (fun hh : b = x ∧ d = x => h2 (hh.1.trans hh.2.symm))]
      simp
  · simp [h1]

theorem solution :
    (∃ Phi : Map 4, FixedChannelFeasible Phi) ∧
    ∃ J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ, FixedChoiFeasible J := by
  refine ⟨⟨krausApply g53g_E, ⟨⟨16, g53g_E, g53g_kraus, fun _ => rfl⟩, ?_, ?_⟩, ?_⟩,
    ⟨choi (krausApply g53g_E), ?_⟩⟩
  · intro t X
    rw [g53g_apply, g53g_apply]
    ext i j
    by_cases h : i = j
    · subst h; simp [timeEvolution, Matrix.diagonal_apply]
    · simp [timeEvolution, Matrix.diagonal_apply, h]
  · rw [g53g_apply]
    unfold gibbsDensity
    congr 1
    funext x
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← g53g_gw x]; push_cast; rfl
  · rw [g53g_apply]; exact g53g_pop _ rfl
  · rw [g53g_choi]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]
      intro p; exact_mod_cast g53g_T_nonneg p.1 p.2
    · intro u v
      by_cases h : u = v
      · subst h; simp [Matrix.diagonal_apply]; exact_mod_cast g53g_colsum u
      · simp [Matrix.diagonal_apply, h]
    · intro x y
      by_cases h : x = y
      · subst h; simp [Matrix.diagonal_apply]; exact_mod_cast g53g_gw x
      · simp [Matrix.diagonal_apply, h]
    · intro x u y v hne
      rw [Matrix.diagonal_apply, if_neg]
      intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hne rfl
    · have : fromChoi (Matrix.diagonal (fun p : Fin 4 × Fin 4 => (g53g_T p.1 p.2 : ℂ))) fixedRho =
          Matrix.diagonal (fun x => ∑ u, (g53g_T x u : ℂ) * fixedRho u u) := by
        ext x y
        by_cases h : x = y
        · subst h; simp [fromChoi, Matrix.diagonal_apply]
        · simp [fromChoi, Matrix.diagonal_apply, h]
      rw [this]; exact g53g_pop _ rfl
