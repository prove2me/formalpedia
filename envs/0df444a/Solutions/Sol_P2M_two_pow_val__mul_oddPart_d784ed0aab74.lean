-- Prove2me | solution 1 for P2M_two_pow_val__mul_oddPart_d784ed0aab74
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:30.931525+00:00
-- url     : https://prove2.me/submissions/b880c849-a4fc-4fc3-979d-f46115a44d38

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_two_pow_val__dvd_f36ca7a4dc65

set_option autoImplicit false
open Nat
theorem _root_.solution (n : ℕ) : 2 ^ val₂ n * oddPart n = n :=
  mul_div_eq_iff_dvd.mpr (two_pow_val₂_dvd n)
