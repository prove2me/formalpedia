-- Prove2me | solution 1 for ULHC.creach_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:43.595722+00:00
-- url     : https://prove2.me/submissions/ac9bf3bf-4cf5-467a-9c6e-baefcfe3bb70

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_creach_sub_succ
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution {x : Pt} {j k : ℕ} (h : j ≤ k) : creach F x j ⊆ creach F x k := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans creach_sub_succ
end ULHC
