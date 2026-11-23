-- Prove2me | solution 1 for SPP.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:08:23.660681+00:00
-- url     : https://prove2.me/submissions/936adef6-e84d-4858-b091-8afb8e1e0856

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_fpp
import Theorems.Thm_FPP_isUnit


set_option autoImplicit false
open Nat
open SPP
namespace SPP
theorem _root_.solution {n : ℕ} [Fact (1 < n)] {a : ZMod n} (h : SPP n a) :
    IsUnit a :=
  h.fpp.isUnit
end SPP
