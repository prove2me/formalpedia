-- Prove2me | solution 1 for WHAdditivity.Renyi.renyi_tensor_additive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:58:23.504359+00:00
-- url     : https://prove2.me/submissions/cb5111b4-5870-4cbd-96c8-ed955420f176

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi Matrix
open scoped ComplexOrder

lemma trace_cfc_herm {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

lemma eig_sum_conj {ι κ : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (W : Matrix ι ι ℂ) (μ : ι → ℝ)
    (hW : star W * W = 1) (hAW : A = W * diagonal (fun y => ((μ y : ℝ) : ℂ)) * star W) (g : ℝ → ℝ) :
    ∑ i, g (hA.eigenvalues i) = ∑ y, g (μ y) := by
  have hroots : Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val =
      Multiset.map (fun y => ((μ y : ℝ) : ℂ)) Finset.univ.val := by
    rw [← hA.roots_charpoly_eq_eigenvalues]
    have : A.charpoly = (diagonal (fun y => ((μ y : ℝ) : ℂ))).charpoly := by
      rw [hAW, charpoly_mul_comm, ← mul_assoc, hW, one_mul]
    rw [this, charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have := congrArg (fun s => (Multiset.map (fun z : ℂ => g z.re) s).sum) hroots
  simp only [Multiset.map_map] at this
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  convert this using 3 <;> simp

section T
variable {N : ℕ} (d : Fin N → ℕ)

lemma tM_mul (A B : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    tensorMatrix d A * tensorMatrix d B = tensorMatrix d (fun j => A j * B j) := by
  ext y y''
  simp only [tensorMatrix, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (b : Fin (d j)) => A j (y j) b * B j b (y'' j))]

lemma tM_star (A : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    star (tensorMatrix d A) = tensorMatrix d (fun j => star (A j)) := by
  ext y y'
  simp [tensorMatrix, Matrix.star_apply, star_prod]

lemma tM_one : tensorMatrix d (fun j => (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) = 1 := by
  ext y y'
  simp only [tensorMatrix, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.prod_boole]
  by_cases h : y = y'
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h (funext h'))]

lemma tM_diag (v : (j : Fin N) → Fin (d j) → ℂ) :
    tensorMatrix d (fun j => diagonal (v j)) = diagonal (fun y => ∏ j, v j (y j)) := by
  ext y y'
  simp only [tensorMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : y = y'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ y' j := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma tM_trace_cfc (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hρ : ∀ j, (ρ j).IsHermitian) (f : ℝ → ℝ) :
    ∃ hA : (tensorMatrix d ρ).IsHermitian,
      (cfc f (tensorMatrix d ρ)).trace =
        ∑ y : Config d, ((f (∏ j, (hρ j).eigenvalues (y j)) : ℝ) : ℂ) := by
  have hA : (tensorMatrix d ρ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [← Matrix.star_eq_conjTranspose, tM_star]
    congr 1; funext j; exact (hρ j).eq
  refine ⟨hA, ?_⟩
  rw [trace_cfc_herm hA]
  set W := tensorMatrix d (fun j => ((hρ j).eigenvectorUnitary : Matrix (Fin (d j)) (Fin (d j)) ℂ))
  have hW : star W * W = 1 := by
    rw [tM_star, tM_mul]
    simp only [Unitary.coe_star_mul_self]
    exact tM_one d
  have hAW : tensorMatrix d ρ = W * diagonal (fun y => (((∏ j, (hρ j).eigenvalues (y j)) : ℝ) : ℂ)) * star W := by
    have e : ρ = fun j => ((hρ j).eigenvectorUnitary : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
        diagonal (fun i => (((hρ j).eigenvalues i : ℝ) : ℂ)) * star ((hρ j).eigenvectorUnitary : Matrix (Fin (d j)) (Fin (d j)) ℂ) := by
      funext j
      conv_lhs => rw [(hρ j).spectral_theorem, Unitary.conjStarAlgAut_apply]
      rfl
    conv_lhs => rw [e]
    rw [← tM_mul, ← tM_mul, tM_diag, tM_star]
    congr 3; funext y; push_cast; rfl
  have := eig_sum_conj (κ := Unit) hA W _ hW hAW f
  rw [← Complex.ofReal_sum, this, Complex.ofReal_sum]
end T

lemma traceRpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (p : ℝ) :
    traceRpow p A = ∑ i, hA.eigenvalues i ^ p := by
  unfold traceRpow; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

lemma vN_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    vonNeumannEntropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  unfold vonNeumannEntropy; rw [trace_cfc_herm hA]
  rw [Complex.re_sum]; simp

lemma density_eig {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : IsDensity ρ) :
    (∀ i, 0 ≤ hρ.1.isHermitian.eigenvalues i) ∧ ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  refine ⟨fun i => hρ.1.eigenvalues_nonneg i, ?_⟩
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have h2 : ρ.trace = 1 := hρ.2
  have := congrArg Complex.re (h2.symm.trans h)
  simp [Complex.re_sum] at this
  linarith

lemma negMulLog_prod {N : ℕ} (b : Fin N → ℝ) (hb : ∀ j, 0 ≤ b j) :
    Real.negMulLog (∏ j, b j) = ∑ j, (∏ k, b k) * (-Real.log (b j)) := by
  by_cases h : ∀ j, b j ≠ 0
  · rw [Real.negMulLog, Real.log_prod (fun j _ => h j), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  · push Not at h; obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]; simp

theorem solution (N : ℕ) (d : Fin N → ℕ)
    (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) (hρ : ∀ j, IsDensity (ρ j))
    (p : ℝ) (hp : 1 ≤ p) :
    renyiEntropy p (tensorMatrix d ρ) = ∑ j, renyiEntropy p (ρ j) := by
  have hH : ∀ j, (ρ j).IsHermitian := fun j => (hρ j).1.isHermitian
  set a : (j : Fin N) → Fin (d j) → ℝ := fun j i => (hH j).eigenvalues i with ha
  have h0 : ∀ j i, 0 ≤ a j i := fun j i => (density_eig (hρ j)).1 i
  have h1 : ∀ j, ∑ i, a j i = 1 := fun j => (density_eig (hρ j)).2
  unfold renyiEntropy
  split_ifs with hp1
  · -- von Neumann
    obtain ⟨hA, htr⟩ := tM_trace_cfc d ρ hH Real.negMulLog
    have hL : vonNeumannEntropy (tensorMatrix d ρ) =
        ∑ y : Config d, Real.negMulLog (∏ j, a j (y j)) := by
      unfold vonNeumannEntropy; rw [htr, Complex.re_sum]; simp [ha]
    rw [hL]
    simp_rw [vN_eq (hH _)]
    simp_rw [negMulLog_prod _ (fun j => h0 j _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∀ y : Config d, (∏ k, a k (y k)) * (-Real.log (a j (y j))) =
        ∏ k, (a k (y k) * (if k = j then -Real.log (a k (y k)) else 1)) := by
      intro y
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
    simp_rw [e]
    rw [← Fintype.prod_sum (fun k (i : Fin (d k)) => a k i * (if k = j then -Real.log (a k i) else 1))]
    have e2 : ∀ k, (∑ i : Fin (d k), a k i * (if k = j then -Real.log (a k i) else 1)) =
        if k = j then ∑ i : Fin (d k), Real.negMulLog (a k i) else 1 := by
      intro k
      by_cases hk : k = j
      · simp only [hk, if_true, Real.negMulLog]; apply Finset.sum_congr rfl; intro i _; ring
      · simp only [hk, if_false, mul_one]; exact h1 k
    rw [Finset.prod_congr rfl (fun k _ => e2 k), Finset.prod_ite_eq' Finset.univ j,
      if_pos (Finset.mem_univ j)]
  · obtain ⟨hA, htr⟩ := tM_trace_cfc d ρ hH (fun x => x ^ p)
    have hL : traceRpow p (tensorMatrix d ρ) = ∏ j, ∑ i, a j i ^ p := by
      unfold traceRpow; rw [htr, Complex.re_sum]
      simp only [Complex.ofReal_re]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl; intro y _
      exact (Real.finsetProd_rpow _ _ (fun j _ => h0 j (y j)) p).symm
    have hpos : ∀ j, 0 < ∑ i, a j i ^ p := by
      intro j
      obtain ⟨i0, hi0⟩ : ∃ i, 0 < a j i := by
        by_contra h; push Not at h
        have : ∑ i, a j i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 j i)
        linarith [h1 j]
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi0 p)
        (Finset.single_le_sum (f := fun i => a j i ^ p) (fun i _ => Real.rpow_nonneg (h0 j i) p)
          (Finset.mem_univ i0))
    rw [hL, Real.log_prod (fun j _ => (hpos j).ne'), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [traceRpow_eq (hH j)]
