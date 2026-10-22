-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.bb84_tightness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:53:12.620944+00:00
-- url     : https://prove2.me/submissions/a8065c20-3bb4-4dbc-958a-856bb9c96d43

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

open QAlgorithms

def g73b_f {n : ℕ} (θ x : Qubits n) : ℝ :=
  ∏ i, (if θ i then (1/2:ℝ) else if x i then 0 else 1)

theorem g73b_ep {n : ℕ} (θ x : Qubits n) :
    effectProb (pureDensity (tensorBasisColumn bb84Basis θ x)) (pureDensity (zeroKet n)) =
      g73b_f θ x := by
  have h1 : effectProb (pureDensity (tensorBasisColumn bb84Basis θ x)) (pureDensity (zeroKet n)) =
      Complex.normSq (∏ i, bb84Basis (θ i) false (x i)) := by
    simp [effectProb, pureDensity, zeroKet, ket, Matrix.trace, Matrix.mul_apply,
      PiLp.single_apply, tensorBasisColumn, Complex.mul_conj]
    rw [← Complex.mul_re, ← map_prod, Complex.mul_conj, Complex.ofReal_re, map_prod]
  rw [h1, map_prod, g73b_f]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hθ : θ i <;> cases hx : x i <;> simp [bb84Basis, hadamard, Complex.normSq_apply]

def g73b_k {n : ℕ} (θ : Qubits n) : ℕ := (Finset.univ.filter (fun i => θ i = true)).card

theorem g73b_f_eq {n : ℕ} (θ x : Qubits n) :
    g73b_f θ x = (1/2:ℝ)^(g73b_k θ) * (if ∀ i, θ i = true ∨ x i = false then 1 else 0) := by
  have : g73b_f θ x = ∏ i, ((if θ i = true then (1/2:ℝ) else 1) *
      (if θ i = true ∨ x i = false then 1 else 0)) := by
    unfold g73b_f
    refine Finset.prod_congr rfl fun i _ => ?_
    cases θ i <;> cases x i <;> simp
  rw [this, Finset.prod_mul_distrib, Fintype.prod_boole, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, g73b_k]
  congr

theorem g73b_f_nonneg {n : ℕ} (θ x : Qubits n) : 0 ≤ g73b_f θ x := by
  rw [g73b_f_eq]; positivity

theorem g73b_sum_f {n : ℕ} (θ : Qubits n) : ∑ x, g73b_f θ x = 1 := by
  unfold g73b_f
  have h := Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if θ i = true then (1/2:ℝ) else if b = true then 0 else 1)
  rw [← h]
  refine Finset.prod_eq_one fun i _ => ?_
  cases θ i <;> simp

theorem g73b_shannon {n : ℕ} (θ : Qubits n) :
    shannon (fun x => g73b_f θ x) = g73b_k θ := by
  unfold shannon
  have : ∀ x, g73b_f θ x * Real.logb 2 (g73b_f θ x) = g73b_f θ x * (-(g73b_k θ : ℝ)) := by
    intro x
    rw [g73b_f_eq]
    split_ifs
    · rw [mul_one, Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
      ring
    · simp
  simp_rw [this, ← Finset.sum_mul, g73b_sum_f]
  ring

theorem g73b_sumk (n : ℕ) : ∑ θ : Qubits n, (g73b_k θ : ℝ) = n * 2^n / 2 := by
  have hinv : ∑ θ : Qubits n, (g73b_k θ : ℝ) = ∑ θ : Qubits n, (g73b_k (fun i => !θ i) : ℝ) := by
    refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.ofBijective Bool.not
      (Function.Involutive.bijective Bool.not_not)) _ _ (fun θ => ?_)
    simp [g73b_k]
  have hadd : ∀ θ : Qubits n, (g73b_k θ : ℝ) + g73b_k (fun i => !θ i) = n := by
    intro θ
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => θ i = true)
    simp only [g73b_k, Bool.not_eq_true']
    simp at this
    exact_mod_cast this
  have : 2 * ∑ θ : Qubits n, (g73b_k θ : ℝ) = n * 2^n := by
    rw [two_mul]
    nth_rewrite 2 [hinv]
    rw [← Finset.sum_add_distrib]
    simp_rw [hadd]
    simp
    ring
  linarith

theorem g73b_density (n : ℕ) : IsDensityMatrix (pureDensity (zeroKet n)) := by
  have h : pureDensity (zeroKet n) = Matrix.diagonal (fun a => if a = (fun _ => false) then 1 else 0) := by
    ext a b
    by_cases ha : a = (fun _ => false) <;> by_cases hb : b = (fun _ => false) <;>
      simp [pureDensity, zeroKet, ket, PiLp.single_apply, Matrix.diagonal, ha, hb]
    exact fun h => hb h.symm
  rw [h]
  refine ⟨?_, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i; split_ifs <;> simp
  · simp [Matrix.trace_diagonal]

theorem g73b_p (n : ℕ) (w : Qubits n × Qubits n) :
    measurementExperiment bb84Basis (pureDensity (zeroKet n)) w =
      ENNReal.ofReal ((1/2:ℝ)^n * g73b_f w.2 w.1) := by
  unfold measurementExperiment
  rw [g73b_ep, ENNReal.ofReal_mul (by positivity)]
  congr 2
  simp

theorem g73b_mass (n : ℕ) (θ : Qubits n) :
    massAt (measurementExperiment bb84Basis (pureDensity (zeroKet n))) Prod.snd θ =
      ENNReal.ofReal ((1/2:ℝ)^n) := by
  unfold massAt
  simp_rw [g73b_p]
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (by positivity) (g73b_f_nonneg θ x)),
    ← Finset.mul_sum, g73b_sum_f, mul_one]

theorem g73b_joint (n : ℕ) (x θ : Qubits n) :
    massAt (measurementExperiment bb84Basis (pureDensity (zeroKet n))) (fun w => (w.1, w.2)) (x, θ) =
      ENNReal.ofReal ((1/2:ℝ)^n * g73b_f θ x) := by
  unfold massAt
  simp_rw [g73b_p]
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp [Prod.mk.injEq, ite_and]

theorem solution (n : ℕ) :
    IsDensityMatrix (pureDensity (zeroKet n)) ∧
    conditionalShannon (measurementExperiment bb84Basis (pureDensity (zeroKet n))) =
      (n : ℝ)/2 := by
  refine ⟨g73b_density n, ?_⟩
  unfold conditionalShannon retainedConditional
  have hc : (0:ℝ) < (1/2)^n := by positivity
  have hm : ∀ θ : Qubits n, massAt (measurementExperiment bb84Basis (pureDensity (zeroKet n))) Prod.snd θ ≠ 0 := by
    intro θ; rw [g73b_mass]; simp
  simp only [hm, if_neg not_false]
  simp only [g73b_mass, g73b_joint]
  have : ∀ θ x : Qubits n, (ENNReal.ofReal ((1/2:ℝ)^n * g73b_f θ x) / ENNReal.ofReal ((1/2:ℝ)^n)).toReal
      = g73b_f θ x := by
    intro θ x
    have := g73b_f_nonneg θ x
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (mul_nonneg hc.le this), ENNReal.toReal_ofReal hc.le]
    field_simp
  simp_rw [this, g73b_shannon, ENNReal.toReal_ofReal hc.le, ← Finset.mul_sum, g73b_sumk]
  field_simp
  rw [mul_comm ((1/2:ℝ)^n), mul_assoc, ← mul_pow]
  norm_num
