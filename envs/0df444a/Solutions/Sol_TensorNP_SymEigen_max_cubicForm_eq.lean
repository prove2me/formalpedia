-- Prove2me | solution 1 for TensorNP.SymEigen.max_cubicForm_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:36:04.400014+00:00
-- url     : https://prove2.me/submissions/18d94d24-be27-47fd-bcec-6dfb641e6954
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TensorNP_SymEigen_Defs
import Definitions.Def_TensorNP_SymEigen_StabTensor
import Theorems.Thm_TensorNP_SymEigen_stabTensor_symmetric_cubicForm
import Theorems.Thm_TensorNP_SymEigen_theorem_9_2

open TensorNP.SymEigen

private lemma l2norm_idx_eq_one_iff {v : ℕ} (z : Idx v → ℝ) :
    l2norm z = 1 ↔ ∑ i : Fin v, z (Sum.inl i) ^ 2 + ∑ p : PairIdx v, z (Sum.inr p) ^ 2 = 1 := by
  unfold l2norm
  rw [Real.sqrt_eq_one, Fintype.sum_sum_type]

private lemma six_mul_M_eq_lambdaL (l : ℕ) (M : ℝ)
    (hEq : Real.sqrt (1 - 1 / (l : ℝ)) = 3 * Real.sqrt (3 / 2) * M) :
    6 * M = lambdaL l := by
  unfold lambdaL
  rw [Real.sqrt_mul (by positivity), hEq]
  have h1 : Real.sqrt (2 / 3) * (3 * Real.sqrt (3 / 2) * M) =
      3 * (Real.sqrt (2 / 3) * Real.sqrt (3 / 2)) * M := by ring
  rw [h1, ← Real.sqrt_mul (by positivity)]
  have h2 : (2 / 3 : ℝ) * (3 / 2) = 1 := by norm_num
  rw [h2, Real.sqrt_one]
  ring

theorem solution {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) :
    IsGreatest {t : ℝ | ∃ z : Idx v → ℝ, l2norm z = 1 ∧ t = cubicForm (stabTensor G) z}
      (lambdaL G.indepNum) := by
  rcases theorem_9_2 hv G with ⟨M, ⟨⟨x₀, y₀, hxy₀, rfl⟩, hM_ub⟩, hEq⟩
  rw [← six_mul_M_eq_lambdaL G.indepNum _ hEq]
  constructor
  · refine ⟨Sum.elim x₀ y₀, ?_, ?_⟩
    · rw [l2norm_idx_eq_one_iff]
      simpa using hxy₀
    · rw [(stabTensor_symmetric_cubicForm G).2]
      simp
  · rintro t ⟨z, hz, rfl⟩
    rw [l2norm_idx_eq_one_iff] at hz
    rw [(stabTensor_symmetric_cubicForm G).2]
    have hle : nesterovForm G (fun i => z (Sum.inl i)) (fun p => z (Sum.inr p)) ≤
        nesterovForm G x₀ y₀ :=
      hM_ub ⟨fun i => z (Sum.inl i), fun p => z (Sum.inr p), hz, rfl⟩
    linarith
