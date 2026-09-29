-- Prove2me | solution 1 for Zeta23.MV.mvDiag_of_eigenBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:20:41.445061+00:00
-- url     : https://prove2.me/submissions/dfadd8f7-ee74-4335-bf11-04f693af2363

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_MV
import Definitions.Def_Zeta23_MV_Duality
import Definitions.Def_Zeta23_MV_Spacing
import Theorems.Thm_Zeta23_MV_abs_eigenvalue_le
import Theorems.Thm_Zeta23_MV_star_dotProduct_mulVec_eq

-- from Zeta23.MV.Duality
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 4 — spectral reduction: `eigen_bound` ⇒ `MVDiag 13` ⇒ `∃ C, MVHilbert C`

With `k_{rs} := √δ_r √δ_s/(λ_r − λ_s)` (0 on the diagonal; real antisymmetric) the matrix
`M := i·K` is Hermitian.  Every eigen-pair `(ν, v)` of `M` (unit `v`, from Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`) satisfies the eigen-relation of `eigen_bound` with `μ := −ν`,
so `|ν| ≤ 13` for all eigenvalues (step 3).  Expanding in the eigenbasis
(`y* M y = Σ_i ν_i |(U*y)_i|²`, `Σ_i |(U*y)_i|² = Σ_i |y_i|²`) gives `|y* M y| ≤ 13 ‖y‖²`;
substituting `y_r := x_r/√δ_r` lands exactly on `MVDiag 13` (the literature / diagonal form of the
Montgomery–Vaughan weighted Hilbert inequality, Zeta23/MV.lean), and polarization
`exists_MVHilbert_of_diag` yields the bilinear H-MV of `Hypotheses.lean`.
-/

noncomputable section

open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV


variable {ι : Type} [Fintype ι] [DecidableEq ι]





omit [DecidableEq ι] in
/-- `star v ⬝ᵥ v = Σ ‖v_i‖²` (as a complex number). -/
lemma star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl


/-- `Σ ‖(U* x)_i‖² = Σ ‖x_i‖²` for the eigenvector unitary `U`. -/
lemma sum_norm_sq_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  have h : star c ⬝ᵥ c = star x ⬝ᵥ x := by
    have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    rw [← hsc, hc_def, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at h
  exact_mod_cast h


/-- The Hermitian form of `M` is bounded by `C ‖y‖²`. -/
lemma norm_form_le {C : ℝ} (hb : EigenBound C) {freq δ : ι → ℝ} (h : Adm freq δ) (y : ι → ℂ) :
    ‖star y ⬝ᵥ (Mmat freq δ *ᵥ y)‖ ≤ C * ∑ i, ‖y i‖ ^ 2 := by
  set hM := Mmat_isHermitian freq δ
  rw [star_dotProduct_mulVec_eq hM, Complex.norm_real, Real.norm_eq_abs, ← sum_norm_sq_unitary hM y,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (abs_eigenvalue_le hb h i) (sq_nonneg _)



end MV
end Zeta23

end
open Finset Complex Matrix Unitary
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution {C : ℝ} (hb : EigenBound C) : MVDiag C := by
  intro ι _ _ freq δ x hinj hpos hadm
  have h : Adm freq δ := ⟨hinj, hpos, hadm⟩
  -- y_r := x_r / √δ_r
  set y : ι → ℂ := fun r => x r / (Real.sqrt (δ r) : ℂ) with hydef
  have hsq : ∀ r, (Real.sqrt (δ r) : ℂ) ≠ 0 := fun r => by
    exact_mod_cast (Real.sqrt_pos.mpr (hpos r)).ne'
  have hxy : ∀ r, x r = (Real.sqrt (δ r) : ℂ) * y r := fun r => by
    simp only [hydef]; field_simp [hsq r]
  -- Σ ‖y_r‖² = Σ ‖x_r‖²/δ_r
  have hnorm : ∑ r, ‖y r‖ ^ 2 = ∑ r, ‖x r‖ ^ 2 / δ r := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hydef, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (hpos r).le]
  -- the double sum is rewritten termwise:
  -- Σ_{r,s} [r≠s] x_r x̄_s/(λ_r−λ_s) = Σ_r Σ_s y_r conj(y_s) k_{rs}
  have hterm : ∀ r s, (if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = y r * conj (y s) * (kfun freq δ r s : ℂ) := by
    intro r s
    by_cases hrs : r = s
    · simp [hrs, kfun]
    · rw [if_neg hrs]
      simp only [kfun, if_neg hrs, hxy r, hxy s, map_mul, Complex.conj_ofReal]
      have hf : ((freq r - freq s : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (fun e => hrs (hinj e))
      push_cast
      field_simp
  have hsum : (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ))
      = conj (star y ⬝ᵥ (Mmat freq δ *ᵥ y)) * Complex.I := by
    simp only [hterm, dotProduct, Matrix.mulVec, Mmat, Pi.star_apply, Complex.star_def, map_sum,
      map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (y r * conj (y s) * (kfun freq δ r s : ℂ)) * this
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_conj, ← hnorm]
  exact norm_form_le hb h y
