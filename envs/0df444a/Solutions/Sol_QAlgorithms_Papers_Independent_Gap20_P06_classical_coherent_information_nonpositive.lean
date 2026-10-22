-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.classical_coherent_information_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:39:25.426058+00:00
-- url     : https://prove2.me/submissions/cb1beb1f-66b0-49c2-ac81-f2fd3952014b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g73c_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73c_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73c_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73c_diag_herm d
  rw [g73c_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g73c_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73c_trace_cfc_diag]
  simp

lemma g73c_traceLeft_diag {R Q : Type*} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (p : R × Q → ℝ) :
    traceLeft (Matrix.diagonal (fun z => (p z : ℂ))) =
      Matrix.diagonal (fun q => ((∑ r, p (r, q) : ℝ) : ℂ)) := by
  ext a b
  simp only [traceLeft, Matrix.of_apply, Matrix.diagonal_apply, Prod.mk.injEq, true_and]
  split_ifs with h
  · subst h; push_cast; rfl
  · simp

lemma g73c_term {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a * Real.logb 2 a ≤ a * Real.logb 2 b := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · exact mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num) h hab) ha

/-- PDF pp.9,18: for an arbitrary finite classical joint probability law,
the entropy of Q minus that of RQ is nonpositive. Diagonal states and their
marginal are constructed from the law, not assumed to satisfy an entropy bound. -/
theorem solution {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (p : R × Q → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    let joint : Matrix (R × Q) (R × Q) ℂ := Matrix.diagonal (fun z => (p z : ℂ))
    vnEntropy (traceLeft joint) - vnEntropy joint ≤ 0 := by
  intro joint
  simp only [joint]
  rw [g73c_traceLeft_diag, g73c_vn_diag, g73c_vn_diag]
  have key : ∑ z, p z * Real.logb 2 (p z) ≤
      ∑ q, (∑ r, p (r, q)) * Real.logb 2 (∑ r, p (r, q)) := by
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_le_sum
    intro q _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r _
    apply g73c_term (hp _)
    exact Finset.single_le_sum (f := fun r => p (r, q)) (fun r _ => hp (r, q)) (Finset.mem_univ r)
  linarith
