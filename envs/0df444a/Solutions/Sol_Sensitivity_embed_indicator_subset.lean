-- Prove2me | solution 1 for Sensitivity.embed_indicator_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:57:23.241388+00:00
-- url     : https://prove2.me/submissions/80e0f6df-7d6c-4a71-92c6-3ca62fa7f0a2

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (free S T : Finset (Fin n))
    (hS : S ⊆ free) (hT : T ⊆ S) :
    embed free (fun _ => false) (indicator T) = indicator T := by
  funext j
  simp only [embed]
  by_cases hj : j ∈ free
  · simp [hj]
  · simp [hj, indicator]
    intro hjT
    exact absurd (hS (hT hjT)) hj
end Sensitivity
