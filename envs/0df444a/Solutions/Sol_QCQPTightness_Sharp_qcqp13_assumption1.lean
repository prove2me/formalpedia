-- Prove2me | solution 1 for QCQPTightness.Sharp.qcqp13_assumption1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:35:29.536534+00:00
-- url     : https://prove2.me/submissions/8ea24ae4-9060-43cc-84f6-e24bd6171770

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Mult
import Definitions.Def_QCQPTightness_Sharp_Examples

open QCQPTightness.Sharp Matrix

theorem solution (n k : ℕ) (hn : 0 < n) : (qcqp13 n k hn).Assumption1 := by
  refine ⟨⟨0, ?_⟩, ⟨Fin.cases (2 : ℝ) (fun _ => 0), ?_, ?_⟩⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [QCQP.q, QCQP.IsIneq, QCQPTightness.ConvHull.quad, qcqp13]
    · simp [QCQP.q, QCQP.IsIneq, QCQPTightness.ConvHull.quad, qcqp13]
  · intro i _
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · set e := blockEquiv (Nat.mul_comm k n)
    have hA : (qcqp13 n k hn).Aγ (Fin.cases (2 : ℝ) (fun _ => 0)) =
        diagonal (fun i => 1 * (-(Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ)) (e.symm i).2 + 2) := by
      have h1 : (-(Matrix.single (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : ℝ))) =
          diagonal (-(Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ))) := by
        rw [← diagonal_single, diagonal_neg]; rfl
      have h2 : kronId k (-(Matrix.single (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : ℝ))) =
          diagonal (fun ij : Fin k × Fin n => 1 * (-(Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Fin n → ℝ)) ij.2) := by
        rw [kronId, h1, ← diagonal_one, kroneckerMap_diagonal_diagonal _ (fun _ => zero_mul _)
          (fun _ => mul_zero _)]
      simp only [QCQP.Aγ, qcqp13, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, zero_smul,
        Finset.sum_const_zero, add_zero]
      rw [h2, Matrix.reindex_apply, submatrix_diagonal_equiv]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [e]
      · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [hA, posDef_diagonal_iff]
    intro i
    simp only [Pi.neg_apply, Pi.single_apply]
    split_ifs <;> norm_num
