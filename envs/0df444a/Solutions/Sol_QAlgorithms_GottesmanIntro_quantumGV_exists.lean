-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.quantumGV_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:03:39.263974+00:00
-- url     : https://prove2.me/submissions/816c392a-2d5f-44a0-8522-e7bd777ff456
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Theorems.Thm_QAlgorithms_GottesmanIntro_quantumGV_nondegenerate_exists

set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.GottesmanIntro
open scoped Matrix

theorem solution :
    ∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)), IsQCode n k d C := by
  intro n k d hd hgv
  obtain ⟨C, hC, _⟩ := quantumGV_nondegenerate_exists n k d hd hgv
  exact ⟨C, hC⟩
