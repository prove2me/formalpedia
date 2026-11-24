-- Prove2me | solution 1 for ULHC.creach_sub_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:40.961043+00:00
-- url     : https://prove2.me/submissions/b3f65c25-8d09-4165-af8b-8f9e3d6742b0

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_creach_succ

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution {x : Pt} {k : ℕ} : creach F x k ⊆ creach F x (k + 1) := by
  rw [creach_succ]; exact subset_union_left
end ULHC
