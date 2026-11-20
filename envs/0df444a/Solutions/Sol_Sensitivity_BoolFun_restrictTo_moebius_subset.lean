-- Prove2me | solution 1 for Sensitivity.BoolFun.restrictTo_moebius_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:57:57.410881+00:00
-- url     : https://prove2.me/submissions/3b68cb7e-c939-4c1c-ba97-a13e3d6c10f4

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Definitions.Def_Sensitivity_Subcube
import Theorems.Thm_Sensitivity_embed_indicator_subset

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (free : Finset (Fin n))
    (S : Finset (Fin n)) (hS : S ⊆ free) :
    (f.restrictTo free (fun _ => false)).moebius S = f.moebius S := by
  unfold moebius restrictTo
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  congr 1
  rw [embed_indicator_subset free S T hS hT]
end BoolFun
end Sensitivity
