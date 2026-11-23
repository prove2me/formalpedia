-- Prove2me | solution 1 for P2M_val__of_odd_644e63334571
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:36.201805+00:00
-- url     : https://prove2.me/submissions/661aac8a-6376-4d20-ac40-74d287e7a333

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2

set_option autoImplicit false
open Nat
variable {n : ℕ}
theorem _root_.solution (h : Odd n) : val₂ n = 0 :=
  padicValNat.eq_zero_of_not_dvd h.not_two_dvd_nat
