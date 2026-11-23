-- Prove2me | solution 1 for P2M_SPP_le_s__81aa0fe3ef1b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:37.298686+00:00
-- url     : https://prove2.me/submissions/29d3d39d-3b0f-4e51-b831-be625e4491c2

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
theorem _root_.solution {s : ℕ} {a : (ZMod n)ˣ} (hs : s < val₂ (n - 1))
    (ha : a ^ (2 ^ s * oddPart (n - 1)) = -1) : s ≤ s₀ n :=
  le_findGreatest (le_pred_of_lt hs) ⟨a, ha⟩
end SPP
