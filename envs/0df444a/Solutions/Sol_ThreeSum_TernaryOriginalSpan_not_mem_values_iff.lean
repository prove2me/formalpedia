-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpan.not_mem_values_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:17.453163+00:00
-- url     : https://prove2.me/submissions/203a65a1-6abd-41ce-838b-7e72f2eeaba4

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Theorems.Thm_ThreeSum_TernaryOriginalSpan_mem_values

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]
namespace ThreeSum.TernaryOriginalSpan
theorem _root_.solution (rows : List V) (v : V) :
    v ∉ values K rows ↔ v ∉ Submodule.span K {w | w ∈ rows} :=
  not_congr (mem_values rows v)
end ThreeSum.TernaryOriginalSpan
