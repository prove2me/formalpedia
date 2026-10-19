-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.polarizedSinglet_inseparable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:02:53.680665+00:00
-- url     : https://prove2.me/submissions/308009d2-d20b-4da9-af99-d7c311f01756

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P01
open QAlgorithms.Entanglement

/-- Peres PDF p.4, Eq. (15) and the following paragraph: every positive singlet
fraction gives a negative partial-transpose eigenvalue and an inseparable state. -/
theorem gp_ps_peres {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) (h : IsSeparableDensity X) :
    (partialTransposeFirst X).PosSemidef := by
  obtain ⟨q, w, A, B, hw, -, hAB, rfl⟩ := h
  have : partialTransposeFirst (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
      ∑ j, (w j : ℂ) • Matrix.kronecker (A j)ᵀ (B j) := by
    ext p r
    simp [partialTransposeFirst, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ =>
    ((hAB j).1.1.transpose.kronecker (hAB j).2.1).smul (Complex.zero_le_real.mpr (hw j))

theorem gp_ps_psd_of_asc {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : M.IsHermitian) (hk : ∀ k, 0 ≤ ascEigenvalues M k) : M.PosSemidef := by
  rw [h.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have := hk (Fin.rev ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))
  simp only [ascEigenvalues, h, dif_pos, Fin.rev_rev] at this
  exact this

theorem solution (x : ℝ) (positive : 0 < x) (fraction : x ≤ 1) :
    (∃ k, ascEigenvalues (partialTransposeFirst (polarizedSingletDensity x)) k < 0) ∧
      ¬ IsSeparableDensity (polarizedSingletDensity x) := by
  set M := partialTransposeFirst (polarizedSingletDensity x) with hM
  have hHerm : M.IsHermitian := by
    ext p q
    rcases p with ⟨_ | _, _ | _⟩ <;> rcases q with ⟨_ | _, _ | _⟩ <;>
      simp [hM, partialTransposeFirst, polarizedSingletDensity, singletDensity, pureDensity, ket,
        PiLp.single_apply]
  have hnot : ¬ M.PosSemidef := by
    intro hpsd
    have := hpsd.re_dotProduct_nonneg
      (fun p => if p = (false, false) then (x : ℂ) else if p = (true, true) then 1 else 0)
    simp [hM, partialTransposeFirst, polarizedSingletDensity, singletDensity, pureDensity, ket,
        PiLp.single_apply, dotProduct, Matrix.mulVec, Fintype.sum_prod_type] at this
    nlinarith [pow_pos positive 3, mul_pos positive positive]
  refine ⟨?_, fun hs => hnot (gp_ps_peres _ hs)⟩
  by_contra hc
  push Not at hc
  exact hnot (gp_ps_psd_of_asc M hHerm hc)

