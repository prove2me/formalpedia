-- Prove2me | solution 1 for Sqrt6KissingBound.regularHexagon_isKissingConfiguration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:30:07.514979+00:00
-- url     : https://prove2.me/submissions/81c14abf-4d24-46dd-9a4a-7d7c098d0853

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_hexPoint_norm
import Theorems.Thm_Sqrt6KissingBound_hexPoint_separated

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution :
    IsKissingConfiguration regularHexagon := by
  classical
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hexPoint_norm i
  · intro x hx z hz hxz
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    apply hexPoint_separated i j
    intro hij
    apply hxz
    exact congrArg hexPoint hij
end Sqrt6KissingBound
