-- Prove2me | solution 1 for Sqrt6KissingBound.hexPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:30:08.581074+00:00
-- url     : https://prove2.me/submissions/047f9630-92ed-4923-b363-8f5dee3f4556

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_hexPoint_norm
import Theorems.Thm_Sqrt6KissingBound_hexPoint_separated

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution : Function.Injective hexPoint := by
  intro i j hij
  by_contra hne
  have hsep := hexPoint_separated i j hne
  have hinner : inner ℝ (hexPoint i) (hexPoint j) = 1 := by
    rw [hij, real_inner_self_eq_norm_sq, hexPoint_norm]
    norm_num
  linarith
end Sqrt6KissingBound
