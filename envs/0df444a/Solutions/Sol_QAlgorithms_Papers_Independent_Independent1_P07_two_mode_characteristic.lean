-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.two_mode_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:58:57.890689+00:00
-- url     : https://prove2.me/submissions/73febb1f-854e-4d46-b7ef-233e9eac3274

import Mathlib
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P07
open Entanglement

/-- Eq. (64), PDF p. 9, retaining its plus sign. Printed: the standard block
has lower-left +1, and the nearby roots are written as real pairs. Changed: use
lower-left -1 in symplecticTwo. Why: Eq. (54) requires antisymmetry and the
earlier normal-mode paragraph gives imaginary root pairs. No coefficient of
the displayed characteristic polynomial is changed. -/
theorem gq_det4 {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) : M.det =
  M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
  - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
  + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
  - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp (config := {decide := true}) [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
  ring

theorem gq_symp_inv : symplecticTwo⁻¹ = -symplecticTwo := by
  apply Matrix.inv_eq_left_inv
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;>
    simp [symplecticTwo, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem gq_cp4 (a b c d e f g h k l : ℝ) :
    (!![b, -c, k, l; a, -b, g, h; -h, l, -e, -f; g, -k, d, e] : Matrix (Fin 4) (Fin 4) ℝ).charpoly =
      Polynomial.X^4 + Polynomial.C ((a*c-b*b)+(d*f-e*e)-2*(g*l-h*k))*Polynomial.X^2 +
        Polynomial.C ((!![a, b, g, h; b, c, k, l; g, k, d, e; h, l, e, f] : Matrix (Fin 4) (Fin 4) ℝ).det) := by
  rw [Matrix.charpoly, gq_det4, gq_det4]
  simp [Matrix.charmatrix_apply, Matrix.one_apply]
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, Polynomial.C_ofNat]
  ring

theorem solution (A B C : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hpositive : (Matrix.fromBlocks A C C.transpose B).PosDef)
    (hphysical : ((Matrix.fromBlocks A C C.transpose B).map (algebraMap ℝ ℂ) +
      (Complex.I/2) • symplecticTwo.map (algebraMap ℝ ℂ)).PosSemidef) :
    let gamma := Matrix.fromBlocks A C C.transpose B
    let gammaTA := momentumReversal*gamma*momentumReversal
    (symplecticTwo⁻¹*gammaTA).charpoly =
      Polynomial.X^4+Polynomial.C (A.det+B.det-2*C.det)*Polynomial.X^2+
        Polynomial.C gamma.det := by
  intro gamma gammaTA
  rw [gq_symp_inv, ← Matrix.charpoly_reindex finSumFinEquiv]
  have hg : gamma.det = (Matrix.reindex finSumFinEquiv finSumFinEquiv gamma).det :=
    (Matrix.det_reindex_self _ _).symm
  have hAs : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  have hBs : B 1 0 = B 0 1 := by simpa using congrFun (congrFun hB 0) 1
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := rfl
  have h1 : Matrix.reindex finSumFinEquiv finSumFinEquiv (-symplecticTwo * gammaTA) =
      !![A 0 1, -A 1 1, C 1 0, C 1 1; A 0 0, -A 0 1, C 0 0, C 0 1;
        -C 0 1, C 1 1, -B 0 1, -B 1 1; C 0 0, -C 1 0, B 0 0, B 0 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaTA, gamma, symplecticTwo, momentumReversal, Matrix.fromBlocks,
        Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal, Matrix.reindex_apply, e0, e1, e2, e3,
        hAs, hBs]
  have h2 : Matrix.reindex finSumFinEquiv finSumFinEquiv gamma =
      !![A 0 0, A 0 1, C 0 0, C 0 1; A 0 1, A 1 1, C 1 0, C 1 1;
        C 0 0, C 1 0, B 0 0, B 0 1; C 0 1, C 1 1, B 0 1, B 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gamma, Matrix.fromBlocks, Matrix.reindex_apply, e0, e1, e2, e3, hAs, hBs]
  rw [hg, h1, h2, gq_cp4, Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_fin_two, hBs, hAs]

