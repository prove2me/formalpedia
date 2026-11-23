-- Prove2me | solution 1 for P2M_val__of_even_abec3e74f714
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:37.289176+00:00
-- url     : https://prove2.me/submissions/19505f78-287a-42fb-afd6-101b823b5447

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2

set_option autoImplicit false
open Nat
variable {n : ℕ}
theorem _root_.solution [hn : NeZero n] (h : Even n) : 0 < val₂ n :=
  pos_iff_ne_zero.mpr ((dvd_iff_padicValNat_ne_zero hn.out).mp h.two_dvd)
