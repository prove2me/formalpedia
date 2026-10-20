-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.depolarizing_channel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:44:45.913837+00:00
-- url     : https://prove2.me/submissions/63e12197-1de2-47c9-8f7a-8f8b87dca12c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct
open QAlgorithms.Papers.Independent.Frontier18.P17
open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)
open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

lemma g52_sq (a : ℝ) (ha : 0 ≤ a) :
    ((Real.sqrt a / 2 : ℝ) : ℂ) * ((Real.sqrt a / 2 : ℝ) : ℂ) = ((a / 4 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]; congr 1
  rw [div_mul_div_comm, Real.mul_self_sqrt ha]; ring

lemma g52_dep_kraus (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QAlgorithms.IsKrausFamily (depolarizingKraus p) := by
  have h1 := g52_sq (1 + 3 * p) (by linarith)
  have h2 := g52_sq (1 - p) (by linarith)
  unfold QAlgorithms.IsKrausFamily
  rw [Fin.sum_univ_four]
  ext i j
  cases i <;> cases j <;>
    simp [depolarizingKraus, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_bool] <;>
    simp only [← mul_assoc, h1, h2] <;> push_cast <;> ring_nf <;> simp [Complex.ext_iff] <;>
    simp only [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + p * 3),
      Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - p), Complex.ofReal_re, Complex.ofReal_im] <;>
    constructor <;> ring



lemma g52_dep_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Matrix Bool Bool ℂ) :
    depolarizing p X = QAlgorithms.krausApply (depolarizingKraus p) X := by
  have h1 := g52_sq (1 + 3 * p) (by linarith)
  have h2 := g52_sq (1 - p) (by linarith)
  unfold QAlgorithms.krausApply
  rw [Fin.sum_univ_four]
  ext i j
  cases i <;> cases j <;>
    simp [depolarizing, depolarizingKraus, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool, Matrix.trace] <;>
    ring_nf <;>
    simp only [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + p * 3),
      Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - p)] <;>
    push_cast <;> ring_nf <;> simp [Complex.ext_iff] <;> ring_nf <;> simp

lemma g52_dyn (p : ℝ) :
    dynamical (depolarizing p) = (fun x y =>
      if x = y then (if x.1 = x.2 then ((1+p : ℝ) : ℂ)/2 else ((1-p : ℝ) : ℂ)/2)
      else if x.1 = x.2 ∧ y.1 = y.2 then (p : ℂ) else 0) := by
  funext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [dynamical, depolarizing, Matrix.trace, Fintype.sum_bool, Matrix.single_apply] <;>
    push_cast <;> ring

noncomputable def g52_K (N : ℕ) (p : ℝ) : Option (Fin N × Fin N) → Matrix (Fin N) (Fin N) ℂ
  | none => ((Real.sqrt p : ℝ) : ℂ) • 1
  | some q => ((Real.sqrt ((1 - p) / N) : ℝ) : ℂ) • Matrix.single q.1 q.2 1

lemma g52_qd (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (hN : 0 < N) :
    QAlgorithms.IsChannel (QAlgorithms.QuditFidelity.depolarizingMap N hN (1-p)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hc : (0:ℝ) ≤ (1 - p) / N := div_nonneg (by linarith) hNr.le
  have sp : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  have sc : ((Real.sqrt ((1-p)/N) : ℝ) : ℂ) * ((Real.sqrt ((1-p)/N) : ℝ) : ℂ) = (((1-p)/N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  let e := Fintype.equivFin (Option (Fin N × Fin N))
  refine ⟨Fintype.card (Option (Fin N × Fin N)), fun j => g52_K N p (e.symm j), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Equiv.sum_comp e.symm (fun o => (g52_K N p o)ᴴ * g52_K N p o), Fintype.sum_option]
    ext a b
    simp only [g52_K, Matrix.add_apply, Matrix.sum_apply, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.conjTranspose_single,
      star_one, Matrix.single_mul_single_same, mul_one, Fintype.sum_prod_type]
    simp only [← mul_assoc, sp, sc]
    simp [Matrix.single_apply, Matrix.one_apply, Finset.sum_ite_eq', Finset.sum_const]
    split_ifs with h
    · subst h
      simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hN0 : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      rw [mul_div_cancel₀ _ hN0]; ring
    · rw [zero_add]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ => ?_)
      rw [if_neg]; rintro ⟨h1, h2⟩; exact h (h1.symm.trans h2)
  · intro ρ
    unfold QAlgorithms.krausApply
    rw [Equiv.sum_comp e.symm (fun o => g52_K N p o * ρ * (g52_K N p o)ᴴ), Fintype.sum_option]
    ext a b
    simp only [g52_K, QAlgorithms.QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.sum_apply,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.conjTranspose_single, star_one, Fintype.sum_prod_type]
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, Matrix.trace, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ← mul_assoc, ite_and]
    have sc' : ((Real.sqrt (1 - p) : ℝ) : ℂ) / ((Real.sqrt N : ℝ) : ℂ) *
        (((Real.sqrt (1 - p) : ℝ) : ℂ) / ((Real.sqrt N : ℝ) : ℂ)) = (1 - p) / N := by
      rw [div_mul_div_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt hNr.le]
      push_cast; ring
    rw [sp, sc', ← Finset.mul_sum]
    by_cases h : a = b
    · subst h; simp; ring
    · simp [h, Ne.symm h]

theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ (N : ℕ) (hN : 0 < N),
      QAlgorithms.IsChannel (QAlgorithms.QuditFidelity.depolarizingMap N hN (1-p))) ∧
    QAlgorithms.IsKrausFamily (depolarizingKraus p) ∧
    (∀ rho : Matrix Bool Bool ℂ, QAlgorithms.IsDensityMatrix rho →
      depolarizing p rho = QAlgorithms.krausApply (depolarizingKraus p) rho) ∧
    (∀ a b c : ℝ, let rho : Matrix Bool Bool ℂ := fun i j =>
        if i then (if j then ((1-a : ℝ) : ℂ) else (b : ℂ)-Complex.I*c)
        else (if j then (b : ℂ)+Complex.I*c else (a : ℂ));
      QAlgorithms.IsDensityMatrix rho →
      depolarizing p rho = (fun i j =>
        if i then (if j then ((1/2 - (a-1/2)*p : ℝ) : ℂ) else ((b : ℂ)-Complex.I*c)*p)
        else (if j then ((b : ℂ)+Complex.I*c)*p else ((1/2 + (a-1/2)*p : ℝ) : ℂ)))) ∧
    dynamical (depolarizing p) = (fun x y =>
      if x = y then (if x.1 = x.2 then ((1+p : ℝ) : ℂ)/2 else ((1-p : ℝ) : ℂ)/2)
      else if x.1 = x.2 ∧ y.1 = y.2 then (p : ℂ) else 0) := by
  refine ⟨fun N hN => g52_qd p hp0 hp1 N hN, g52_dep_kraus p hp0 hp1,
    fun rho _ => g52_dep_apply p hp0 hp1 rho, ?_, g52_dyn p⟩
  intro a b c rho _
  funext i j
  cases i <;> cases j <;>
    simp only [depolarizing, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.trace, Fintype.sum_bool, Matrix.diag, smul_eq_mul] <;>
    simp [rho] <;> push_cast <;> ring
