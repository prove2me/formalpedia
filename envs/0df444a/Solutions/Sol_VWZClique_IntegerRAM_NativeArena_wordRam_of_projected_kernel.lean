-- Prove2me | solution 1 for VWZClique.IntegerRAM.NativeArena.wordRam_of_projected_kernel
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:08:13.539717+00:00
-- url     : https://prove2.me/submissions/d1d59d8d-07ea-41cf-b185-2f843f7ba425

import Definitions.Def_VWZClique_NativeProjectionContract
import Theorems.Thm_VWZClique_IntegerRAM_NativeArena_compiled_of_projection
import Theorems.Thm_VWZClique_IntegerRAM_NativeFrame_realizes_of_implemented
import Theorems.Thm_VWZClique_NativeTraversal_wordRam_of_realizes

theorem solution
    {mm : ℕ → ℕ} {T : ℕ} (pk : VWZClique.IntegerRAM.NativeArena.ProjectionKernel mm T)
    {C : ℝ} (hC : 0 < C)
    (rate : ∀ n : ℕ, 1 ≤ n → (mm n : ℝ) ≤ C * (n : ℝ) ^
      (OAI.MatrixMultiplication.Arithmetic.omega ℂ + (VWZClique.UniformFolds.levelSaving 36).val / 8)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ k ≥ K₀,
      VWZClique.countsWithin k ((OAI.MatrixMultiplication.Arithmetic.omega ℂ - δ) * (k : ℝ) / 3) :=
  (VWZClique.IntegerRAM.NativeArena.compiled_of_projection pk).elim fun impl =>
    VWZClique.NativeTraversal.wordRam_of_realizes hC rate (VWZClique.IntegerRAM.NativeFrame.realizes_of_implemented impl)
