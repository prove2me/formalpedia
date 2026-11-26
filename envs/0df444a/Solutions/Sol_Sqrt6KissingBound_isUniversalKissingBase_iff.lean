-- Prove2me | solution 1 for Sqrt6KissingBound.isUniversalKissingBase_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:35:47.69027+00:00
-- url     : https://prove2.me/submissions/399a4df0-dabd-4f77-967d-dafb078bff53

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_sqrt6_le_of_isUniversalKissingBase
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (α : ℝ) :
    IsUniversalKissingBase α ↔ Real.sqrt 6 ≤ α := by
  constructor
  · exact sqrt6_le_of_isUniversalKissingBase
  · intro hα
    refine ⟨(Real.sqrt_nonneg 6).trans hα, ?_⟩
    intro n hn X hX
    exact (kissingConfiguration_card_le_sqrt6_pow hn X hX).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg 6) hα n)
end Sqrt6KissingBound
