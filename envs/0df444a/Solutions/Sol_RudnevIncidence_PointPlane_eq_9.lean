-- Prove2me | solution 1 for RudnevIncidence.PointPlane.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:33.755359+00:00
-- url     : https://prove2.me/submissions/303edfe9-1e60-4ac1-9b54-64a954f099c2

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Fin.VecNotation
import Definitions.Def_RudnevIncidence_PointPlane_Setting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open RudnevIncidence.PointPlane

theorem solution {F : Type*} [Field F] (q u q' u' : Fin 4 → F)
    (h : LinearIndependent F ![q, u]) (h' : LinearIndependent F ![q', u']) :
    Submodule.span F {q, u} ⊓ Submodule.span F {q', u'} ≠ ⊥ ↔
      recip (plucker q u) (plucker q' u') = 0 := by
  classical
  let A : Matrix (Fin 4) (Fin 4) F := ![q,u,q',u']
  have hcomp : A ∘ (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) = Sum.elim ![q,u] ![q',u'] := by
    funext i
    rcases i with i|i <;> fin_cases i <;> rfl
  have hli : LinearIndependent F A ↔ Disjoint (Submodule.span F {q,u}) (Submodule.span F {q',u'}) := by
    rw [← linearIndependent_equiv' (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) hcomp]
    rw [linearIndependent_sum]
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.range_cons_cons_empty,
      h, h', true_and]
  have hdet : A.det = recip (plucker q u) (plucker q' u') := by
    rw [Matrix.det_succ_row_zero]
    simp [A, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ,
      plucker, recip, Fin.succAbove]
    simp [Matrix.submatrix, Fin.succAbove]
    ring
  have hunit : LinearIndependent F A ↔ A.det ≠ 0 := by
    change LinearIndependent F A.row ↔ A.det ≠ 0
    rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hne : Disjoint (Submodule.span F {q,u}) (Submodule.span F {q',u'}) ↔
      recip (plucker q u) (plucker q' u') ≠ 0 := by
    rw [← hli, hunit, hdet]
  simpa only [disjoint_iff, ne_eq, not_not] using not_congr hne

#print axioms solution

