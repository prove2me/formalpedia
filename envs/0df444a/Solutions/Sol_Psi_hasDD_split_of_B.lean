-- Prove2me | solution 1 for Psi.hasDD_split_of_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:32:41.693791+00:00
-- url     : https://prove2.me/submissions/c9466752-2ddd-4309-a60e-7a1037379efa

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_prefix
import Theorems.Thm_Psi_splitAtRow_append_left_fst
import Theorems.Thm_Psi_splitAtRow_append


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (B C : List Bool) (h : ℕ) (hBend : stEast B false = true)
    (hBnum : h ≤ numN B) (hBnoDD : hasDD B = false) :
    hasDD (splitAtRow (B ++ C) h).1 = false := by
  rw [splitAtRow_append_left_fst B C h hBend hBnum]
  exact hasDD_prefix _ _ (by rw [splitAtRow_append]; exact hBnoDD)
end Psi
