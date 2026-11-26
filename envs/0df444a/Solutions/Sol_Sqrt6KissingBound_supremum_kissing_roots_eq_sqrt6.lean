-- Prove2me | solution 1 for Sqrt6KissingBound.supremum_kissing_roots_eq_sqrt6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:36:46.052839+00:00
-- url     : https://prove2.me/submissions/3345b2d9-a13d-4a4f-bde2-07adf497c692

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_card
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_isKissingConfiguration
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_root_le_sqrt6

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution :
    sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} =
      Real.sqrt 6 := by
  have hmem : Real.sqrt 6 ∈
      {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
        IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} := by
    refine ⟨2, by norm_num, regularHexagon, regularHexagon_isKissingConfiguration, ?_⟩
    rw [regularHexagon_card, Real.sqrt_eq_rpow]
    norm_num
  apply le_antisymm
  · apply csSup_le
    · exact ⟨Real.sqrt 6, hmem⟩
    · intro x hx
      rcases hx with ⟨n, hn, X, hX, rfl⟩
      exact kissingConfiguration_root_le_sqrt6 hn X hX
  · apply le_csSup
    · refine ⟨Real.sqrt 6, ?_⟩
      rintro x ⟨n, hn, X, hX, rfl⟩
      exact kissingConfiguration_root_le_sqrt6 hn X hX
    · exact hmem
end Sqrt6KissingBound
