-- Prove2me | solution 1 for SPP.orderOf_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:08.862664+00:00
-- url     : https://prove2.me/submissions/fd706a5a-9001-420d-a11f-6753e870d24b

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_fpp
import Theorems.Thm_FPP_orderOf_dvd_sub_one


set_option autoImplicit false
open Nat
open SPP
namespace SPP
theorem _root_.solution {n : ℕ} {a : ZMod n} (h : SPP n a) :
    orderOf a ∣ n - 1 :=
  h.fpp.orderOf_dvd_sub_one
end SPP
