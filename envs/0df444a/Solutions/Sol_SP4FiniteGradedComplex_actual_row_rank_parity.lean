-- Prove2me | solution 1 for SP4FiniteGradedComplex.actual_row_rank_parity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:03:22.000819+00:00
-- url     : https://prove2.me/submissions/fb44c241-b5cd-4c57-a975-0419fee3f535

import Theorems.Thm_SP4FiniteGradedComplex_rank_polynomial
import Theorems.Thm_SP4GradedLaurent_common_normalization_parity

set_option autoImplicit false
open scoped BigOperators
open SP4FiniteGradedComplex SP4GradedLaurent

theorem solution {K : Type*} [Field K]
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    {Cp Cm : ι → τ → Type*}
    [∀ i j, AddCommGroup (Cp i j)] [∀ i j, Module K (Cp i j)]
    [∀ i j, FiniteDimensional K (Cp i j)]
    [∀ i j, AddCommGroup (Cm i j)] [∀ i j, Module K (Cm i j)]
    [∀ i j, FiniteDimensional K (Cm i j)]
    (Ap : ∀ i, Data K τ (Cp i)) (Am : ∀ i, Data K τ (Cm i))
    (flip : κ ≃ κ) (k : ι → κ → ℤ) (l : ι → ℤ)
    (X0 : κ → GradedPolynomial) (Xp Xm : ι → κ → GradedPolynomial)
    (U0 : GradedPolynomial) (Up Um : ι → GradedPolynomial)
    (G : κ → GradedPolynomial) (lam mu : ℤ)
    (hcell : ∀ i j, euler (Xp i j) = 0)
    (hconj : ∀ i j, Xm i (flip j) = shift (2 * k i j) (Xp i j))
    (htarget : ∀ i, Um i = shift (2 * l i) (Up i))
    (hchainp : ∀ i, chainPolynomial (Ap i) = ∑ j, Xp i j)
    (hchainm : ∀ i, chainPolynomial (Am i) = ∑ j, Xm i j)
    (hhomologyp : ∀ i, homologyPolynomial (Ap i) = tensorV (shift lam (Up i)))
    (hhomologym : ∀ i, homologyPolynomial (Am i) = tensorV (shift lam (Um i)))
    (hrow0 : ∑ j, X0 j = tensorV (shift lam U0))
    (hcolumn : ∀ j, X0 j + ∑ i, Xp i j + ∑ i, Xm i j = tensorV (shift mu (G j)))
    (hU : euler U0 + ∑ i, euler (Up i) + ∑ i, euler (Um i) = 1)
    (hG : ∑ j, euler (G j) = 1)
    (hnorm : tensorV (Finsupp.single lam 1) = tensorV (Finsupp.single mu 1)) :
    lam = mu ∧ Even (∑ i, (Module.finrank K (LinearMap.range (totalD (Ap i))) : ℤ)) := by
  have hp (i : ι) : ∑ j, Xp i j = tensorV (shift lam (Up i)) +
      tensorV (rankPolynomial (Ap i)) := by
    rw [← hchainp i, ← hhomologyp i]
    exact (SP4FiniteGradedComplex.rank_polynomial (Ap i)).2.2.1
  have hm (i : ι) : ∑ j, Xm i j = tensorV (shift lam (Um i)) +
      tensorV (rankPolynomial (Am i)) := by
    rw [← hchainm i, ← hhomologym i]
    exact (SP4FiniteGradedComplex.rank_polynomial (Am i)).2.2.1
  have h := SP4GradedLaurent.common_normalization_parity flip k l X0 Xp Xm U0 Up Um
    (fun i => rankPolynomial (Ap i)) (fun i => rankPolynomial (Am i)) G lam mu
    hcell hconj htarget hrow0 hp hm hcolumn hU hG hnorm
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  congr 1
  funext i
  exact (SP4FiniteGradedComplex.rank_polynomial (Ap i)).2.2.2.1.symm
