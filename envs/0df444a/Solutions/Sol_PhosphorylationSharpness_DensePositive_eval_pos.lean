-- Prove2me | solution 1 for PhosphorylationSharpness.DensePositive.eval_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:24.594877+00:00
-- url     : https://prove2.me/submissions/9bbdf45d-ebd2-4755-a75c-6c99f8912d06

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_DensePositive_nonneg


set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
namespace DensePositive
theorem _root_.solution {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m)
    {u : ℝ} (hu : 0 < u) : 0 < p.eval u := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hp.nonneg i) (pow_nonneg hu.le _)
  · refine ⟨0, by simp, ?_⟩
    simpa using hp.1 0 (by omega)
end DensePositive
end PhosphorylationSharpness
