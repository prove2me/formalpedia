-- Prove2me | solution 1 for SPP.mem_nonwitnessGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:15.584465+00:00
-- url     : https://prove2.me/submissions/c073d528-8746-4aee-b962-75b6010880e2

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution {a : (ZMod n)ˣ} (h : SPP n a) :
    a ∈ nonwitnessGroup n :=
  subset_closure h
end SPP
