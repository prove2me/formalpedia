-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.codeBounds_asymptotic_of_hamming
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:03:38.557195+00:00
-- url     : https://prove2.me/submissions/f908061f-5e8f-4b4c-bbbb-06ba08c04b57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_hamming_asymptotic
import Theorems.Thm_QAlgorithms_GottesmanIntro_codeBounds_gv_asymptotic_params
import Theorems.Thm_QAlgorithms_GottesmanIntro_quantumGV_nondegenerate_exists

set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.GottesmanIntro
open scoped Matrix

theorem solution
    (hamming : ∀ (n k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
      IsNondegenerate C ((d - 1) / 2) →
      (∑ j ∈ Finset.range ((d - 1) / 2 + 1), 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n) :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∀ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C →
        IsNondegenerate C ((d - 1) / 2) → 2 * p * n ≤ d →
        (k : ℝ) / n ≤ 1 - p * Real.logb 2 3 - binEntropy2 p + ε) ∧
      (0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ (k d : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))), IsQCode n k d C ∧
          IsNondegenerate C ((d - 1) / 2) ∧ 2 * p * n ≤ d ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n) := by
  intro p hp0 hp12 ε hε
  obtain ⟨N₁, hN₁⟩ := codeBounds_hamming_asymptotic hamming p hp0 hp12 ε hε
  obtain ⟨N₂, hN₂⟩ := codeBounds_gv_asymptotic_params p hp0 hp12 ε hε
  refine ⟨max N₁ N₂, fun n hn => ⟨hN₁ n (le_trans (le_max_left _ _) hn), fun hrate => ?_⟩⟩
  obtain ⟨k, d, hd1, hd2, hgv, hrate_lb⟩ := hN₂ n (le_trans (le_max_right _ _) hn) hrate
  obtain ⟨C, hC, hnd⟩ := quantumGV_nondegenerate_exists n k d hd1 hgv
  exact ⟨k, d, C, hC, hnd, hd2, hrate_lb⟩
