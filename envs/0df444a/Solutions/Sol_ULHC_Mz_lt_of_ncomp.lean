-- Prove2me | solution 1 for ULHC.Mz_lt_of_ncomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:56.808801+00:00
-- url     : https://prove2.me/submissions/ee57aa08-ec25-42c6-85d7-756809334c37

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_extra_le
import Theorems.Thm_ULHC_Mz_ge
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G G' : Finset Edge} (hG' : Inside V G')
    (h : ncomp V G' + 1 ≤ ncomp V G) : Mz V G' < Mz V G := by
  have h1 := extra_le hG'
  have h2 := Mz_ge (V := V) G
  have h3 : (ncomp V G' + 1) * (2 * Dm V + 4) ≤ ncomp V G * (2 * Dm V + 4) :=
    Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at h3
  omega
end ULHC
