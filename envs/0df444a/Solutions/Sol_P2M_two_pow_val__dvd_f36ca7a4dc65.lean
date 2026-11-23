-- Prove2me | solution 1 for P2M_two_pow_val__dvd_f36ca7a4dc65
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:12.925329+00:00
-- url     : https://prove2.me/submissions/f7ef3303-842c-437f-b7ce-9bedd7681a3f

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2

set_option autoImplicit false
open Nat
theorem _root_.solution (n : ℕ) : 2 ^ val₂ n ∣ n :=
  pow_padicValNat_dvd
