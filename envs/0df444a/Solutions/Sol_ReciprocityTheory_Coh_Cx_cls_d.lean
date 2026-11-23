-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.cls_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.033529+00:00
-- url     : https://prove2.me/submissions/1d04dd20-4017-447e-95bb-e047ba5bfb14

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open ReciprocityTheory.Coh.Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.Cx
theorem _root_.solution {n : ℕ} (y : A.X n) (h : A.d (n + 1) (A.d n y) = 0) :
    A.cls (n + 1) (A.d n y) h = 0 := by
  rw [cls_eq_zero_iff, mem_B_succ]
  exact ⟨y, rfl⟩
end ReciprocityTheory.Coh.Cx
