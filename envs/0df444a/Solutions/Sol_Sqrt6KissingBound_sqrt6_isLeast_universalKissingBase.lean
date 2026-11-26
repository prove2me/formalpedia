-- Prove2me | solution 1 for Sqrt6KissingBound.sqrt6_isLeast_universalKissingBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:36:56.422987+00:00
-- url     : https://prove2.me/submissions/2f2fd5b6-29f7-48bc-85b9-09e0d382ed3a

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_sqrt6_isUniversalKissingBase
import Theorems.Thm_Sqrt6KissingBound_sqrt6_le_of_isUniversalKissingBase

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution :
    IsLeast {α : ℝ | IsUniversalKissingBase α} (Real.sqrt 6) :=
  ⟨sqrt6_isUniversalKissingBase,
    fun _ hα => sqrt6_le_of_isUniversalKissingBase hα⟩
end Sqrt6KissingBound
