-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.division_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:54:34.544138+00:00
-- url     : https://prove2.me/submissions/05eb1e28-f7a1-4895-9c8e-0897524aecf5

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution (free n W nA nB nC J U : ℕ) :
    LightTernarySignedMatrix.space (work free n W nA nB nC J) U≤arenaFree free n W nA nB nC J U ∧
    LightTernaryCarryCodes.space (work free n W nA nB nC J) (2^J)≤arenaFree free n W nA nB nC J U := by
  have hu := Nat.log_le_self 2 (3*U+1)
  have hq := Nat.log_le_self 2 (2^J+1)
  constructor
  · unfold LightTernarySignedMatrix.space LightTernarySignedRow.space LightOutputDecodeDigits.space arenaFree
    apply Nat.add_le_add_left
    calc
      _ ≤ (3*U+1)+2 := Nat.add_le_add_right hu 2
      _ ≤ _ := by nlinarith [Nat.zero_le (2^J)]
  · unfold LightTernaryCarryCodes.space LightOutputDecodeDigits.space arenaFree
    apply Nat.add_le_add_left
    calc
      _ ≤ (2^J+1)+2 := Nat.add_le_add_right hq 2
      _ ≤ _ := by nlinarith [Nat.zero_le (2^J)]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
