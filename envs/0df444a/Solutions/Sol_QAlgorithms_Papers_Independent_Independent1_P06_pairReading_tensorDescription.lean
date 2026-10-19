-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.pairReading_tensorDescription
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:11:03.879034+00:00
-- url     : https://prove2.me/submissions/575d9205-1fab-4c18-94ae-87d9c01c41e4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P06
/-- Lemma 3.3, PDF pp.18–19, with the metacheck term retained as on pp.21–22:
all three coboundaries of Eq.(2), in the displayed tensor-product bases, are precisely
those of C tensor (F2^2 --[1 1]--> F2). The matrix types specify all four degrees. -/


theorem solution {n mx mz : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (css : HX * HZ.transpose = 0) :
    (readingX HX pairPattern).transpose =
      Matrix.fromRows
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) F2) HX.transpose)
        (Matrix.kronecker pairPattern (1 : Matrix (Fin mx) (Fin mx) F2)) ∧
    (readingZ HX HZ pairPattern).transpose =
      Matrix.fromBlocks
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) F2) HZ.transpose)
        (Matrix.kronecker pairPattern.transpose (1 : Matrix (Fin n) (Fin n) F2))
        0 (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) F2) HX) ∧
    (readingMeta HZ pairPattern).transpose =
      Matrix.fromRows
        (Matrix.kronecker pairPattern.transpose (1 : Matrix (Fin mz) (Fin mz) F2))
        (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) F2) HZ.transpose) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    rcases i with ⟨a, q⟩ | ⟨e, x⟩ <;> rcases j with ⟨b, y⟩ <;>
      simp [readingX, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
        pairPattern, eq_comm]
  · ext i j
    rcases i with ⟨a, q⟩ | ⟨e, x⟩ <;> rcases j with ⟨b, y⟩ | ⟨f, z⟩ <;>
      simp [readingZ, Matrix.fromBlocks, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
        pairPattern, eq_comm, Fin.fin_one_eq_zero]
  · ext i j
    rcases i with ⟨a, q⟩ | ⟨e, x⟩ <;> rcases j with ⟨b, y⟩ <;>
      simp [readingMeta, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
        pairPattern, eq_comm, Fin.fin_one_eq_zero]

