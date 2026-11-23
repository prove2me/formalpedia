-- Prove2me | solution 1 for SPP.of_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:14:04.299028+00:00
-- url     : https://prove2.me/submissions/10badfda-1a0c-423d-bdf8-d62f1214039a

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_of_fpp_of_mul_self_eq_one
import Theorems.Thm_FPP_of_prime


set_option autoImplicit false
open Nat
open SPP
namespace SPP
theorem _root_.solution {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    SPP p a :=
  of_fpp_of_mul_self_eq_one (FPP.of_prime ha) (fun _ ↦ mul_self_eq_one_iff.mp)
end SPP
