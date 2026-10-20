-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P63.higherNormCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:25:21.754236+00:00
-- url     : https://prove2.me/submissions/20cf4818-446c-4d7c-b6cd-ca01ed611b40

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory


open Matrix Polynomial in
theorem g53h_eig {n : ℕ} (d : Fin n → ℝ) (hd : Antitone d)
    (h : (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian) :
    h.eigenvalues₀ = fun k => d (Fin.cast (by simp) k) := by
  have h1 := h.sort_roots_charpoly_eq_eigenvalues₀
  rw [charpoly_diagonal, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : ((Finset.univ.val.bind fun i : Fin n => ({((d i : ℝ) : ℂ)} : Multiset ℂ)).map RCLike.re)
      = (List.ofFn d : Multiset ℝ) := by
    rw [Multiset.bind_singleton, Multiset.map_map]
    simp [Fin.univ_val_map]
  rw [h2, Multiset.coe_sort, List.mergeSort_of_pairwise] at h1
  · funext k
    have := congrArg (fun l => l.getD k.val 0) h1
    have hk : k.val < n := by simpa using k.isLt
    simp [hk] at this
    exact this.symm
  · simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hd.sortedGE_ofFn

theorem g53h_eig2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) (hd : Antitone d)
    (hM : M = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) (h : M.IsHermitian) :
    h.eigenvalues₀ = fun k => d (Fin.cast (by simp) k) := by
  subst hM; exact g53h_eig d hd h

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A.1, Eqs.(75)–(77), PDF p.14, and the constant-sequence defect on p.9.
These are the fixed matrices printed in the source, not arbitrary existential witnesses. -/
theorem solution :
    IsDensityMatrix counterX ∧ IsDensityMatrix counterY ∧
    (∀ t : ℝ, 0 < t →
      (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterX)).re -
        (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterY)).re = t/5000 + 161/500000) ∧
    (∀ t : ℝ, 0 < t → 0 < t/5000 + (161/500000 : ℝ)) ∧
    (∀ t : ℝ, 0 < t → logDet t counterY < logDet t counterX) ∧
    (counterX^3).trace.re = (61433/500000 : ℝ) ∧
    (counterY^3).trace.re = (49/400 : ℝ) ∧
    (49/400 : ℝ) < 61433/500000 ∧
    schatten 3 counterY < schatten 3 counterX ∧
    defect counterX counterY = (1/50 : ℝ) := by
  have hXd : counterX = Matrix.diagonal (fun i => (((![42/100, 29/100, 29/100] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    unfold counterX; congr 1; funext i; fin_cases i <;> simp
  have hYd : counterY = Matrix.diagonal (fun i => (((![40/100, 35/100, 25/100] : Fin 3 → ℝ) i : ℝ) : ℂ)) := by
    unfold counterY; congr 1; funext i; fin_cases i <;> simp
  have eX : ∀ j, eigen counterX j = (![42/100, 29/100, 29/100] : Fin 3 → ℝ) (Fin.cast (by simp) j) := by
    intro j
    have hh : counterX.IsHermitian := by
      rw [hXd]; exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
    have hA : Antitone (![42/100, 29/100, 29/100] : Fin 3 → ℝ) := by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> norm_num
    unfold eigen ascEigenvalues
    rw [dif_pos hh, g53h_eig2 _ _ hA hXd hh]
    simp
  have eY : ∀ j, eigen counterY j = (![40/100, 35/100, 25/100] : Fin 3 → ℝ) (Fin.cast (by simp) j) := by
    intro j
    have hh : counterY.IsHermitian := by
      rw [hYd]; exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
    have hA : Antitone (![40/100, 35/100, 25/100] : Fin 3 → ℝ) := by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> norm_num
    unfold eigen ascEigenvalues
    rw [dif_pos hh, g53h_eig2 _ _ hA hYd hh]
    simp
  have hdiag : ∀ (t : ℝ) (v : Fin 3 → ℝ), (t : ℂ) • (1 : Mat (Fin 3)) + Matrix.diagonal (fun i => ((v i : ℝ) : ℂ))
      = Matrix.diagonal (fun i => (((t + v i : ℝ)) : ℂ)) := by
    intro t v; ext i j; by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, h]
  have dX : ∀ t : ℝ, (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterX)).re
      = (t + 42/100) * (t + 29/100) * (t + 29/100) := by
    intro t; rw [hXd, hdiag, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]; simp
  have dY : ∀ t : ℝ, (Matrix.det ((t : ℂ) • (1 : Mat (Fin 3)) + counterY)).re
      = (t + 40/100) * (t + 35/100) * (t + 25/100) := by
    intro t; rw [hYd, hdiag, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]; simp
  have dens : ∀ (M : Mat (Fin 3)) (v : Fin 3 → ℝ), M = Matrix.diagonal (fun i => ((v i : ℝ) : ℂ)) →
      (∀ i, 0 ≤ v i) → M.trace = 1 → IsDensityMatrix M := by
    intro M v hM hv htr
    refine ⟨?_, htr⟩
    rw [hM, Matrix.posSemidef_diagonal_iff]
    intro i; simpa using hv i
  have trX : counterX.trace = 1 := by norm_num [counterX, Matrix.trace, Fin.sum_univ_succ]
  have trY : counterY.trace = 1 := by norm_num [counterY, Matrix.trace, Fin.sum_univ_succ]
  have lX : ∀ k : ℕ, lorenz counterX k = (if 0 < k then 42/100 else 0) + (if 1 < k then 29/100 else 0)
      + (if 2 < k then 29/100 else 0) := by
    intro k; unfold lorenz; simp_rw [eX]
    refine (Fintype.sum_equiv (finCongr (by simp)) _ (fun i : Fin 3 => if i.val < k then (![42/100, 29/100, 29/100] : Fin 3 → ℝ) i else 0)
      (fun x => rfl)).trans ?_
    simp [Fin.sum_univ_three]
  have lY : ∀ k : ℕ, lorenz counterY k = (if 0 < k then 40/100 else 0) + (if 1 < k then 35/100 else 0)
      + (if 2 < k then 25/100 else 0) := by
    intro k; unfold lorenz; simp_rw [eY]
    refine (Fintype.sum_equiv (finCongr (by simp)) _ (fun i : Fin 3 => if i.val < k then (![40/100, 35/100, 25/100] : Fin 3 → ℝ) i else 0)
      (fun x => rfl)).trans ?_
    simp [Fin.sum_univ_three]
  refine ⟨dens _ _ hXd (by intro i; fin_cases i <;> norm_num) trX,
    dens _ _ hYd (by intro i; fin_cases i <;> norm_num) trY, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _; rw [dX, dY]; ring
  · intro t ht; positivity
  · intro t ht; unfold logDet; rw [dX, dY]
    apply Real.log_lt_log (by positivity); nlinarith
  · rw [hXd, Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_three]; simp; norm_num
  · rw [hYd, Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_three]; simp; norm_num
  · norm_num
  · unfold schatten; simp_rw [eX, eY]
    rw [Fin.sum_congr' (fun i : Fin 3 => ((![42/100, 29/100, 29/100] : Fin 3 → ℝ) i) ^ (3:ℝ)),
      Fin.sum_congr' (fun i : Fin 3 => ((![40/100, 35/100, 25/100] : Fin 3 → ℝ) i) ^ (3:ℝ))]
    simp only [Fin.sum_univ_three]
    have h3 : ∀ x : ℝ, x ^ (3:ℝ) = x ^ (3:ℕ) := fun x => by exact_mod_cast Real.rpow_natCast x 3
    simp only [h3]
    apply Real.rpow_lt_rpow (by simp; positivity) (by simp; norm_num) (by norm_num)
  · unfold defect
    apply IsGreatest.csSup_eq
    refine ⟨⟨⟨1, by simp⟩, ?_⟩, ?_⟩
    · simp only [lX, lY]; norm_num
    · rintro _ ⟨k, rfl⟩
      simp only [lX, lY]
      have hk : k.val < 4 := by simpa using k.isLt
      interval_cases (k.val) <;> norm_num

end
