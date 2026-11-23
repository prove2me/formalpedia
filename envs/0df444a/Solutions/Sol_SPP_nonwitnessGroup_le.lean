-- Prove2me | solution 1 for SPP.nonwitnessGroup_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:16.074872+00:00
-- url     : https://prove2.me/submissions/139d745e-cedb-4776-a2b4-d5ca9b0b6fbe

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
theorem _root_.solution (K : Subgroup (ZMod n)ˣ) (h : ∀ a : (ZMod n)ˣ, SPP n a → a ∈ K) :
    nonwitnessGroup n ≤ K :=
  (closure_le K).mpr h
end SPP
