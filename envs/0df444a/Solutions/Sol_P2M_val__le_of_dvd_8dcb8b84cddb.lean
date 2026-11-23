-- Prove2me | solution 1 for P2M_val__le_of_dvd_8dcb8b84cddb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:57.052933+00:00
-- url     : https://prove2.me/submissions/6901c4cc-9ae3-4402-b8d8-81d7cca46012

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_two_pow_val__dvd_f36ca7a4dc65

set_option autoImplicit false
open Nat
variable {n : ℕ}
variable {m : ℕ}
theorem _root_.solution [hn : NeZero n] (h : m ∣ n) : val₂ m ≤ val₂ n :=
  (padicValNat_dvd_iff_le hn.out).mp ((two_pow_val₂_dvd m).trans h)
