-- Prove2me | solution 1 for SPP.H_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:11:38.670509+00:00
-- url     : https://prove2.me/submissions/2b708c74-44a3-45e7-a2e0-d709262aacf2

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
theorem _root_.solution : H (one_dvd n) = ⊤ := by
  apply eq_top_iff.mpr
  intro _ _
  show ZMod.unitsMap (one_dvd n) _ ∈ Subgroup.closure _
  rw [Subsingleton.eq_one (ZMod.unitsMap (one_dvd n) _)]
  exact Subgroup.one_mem _
end SPP
