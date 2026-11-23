-- Prove2me | solution 1 for P2M_SPP_s__lt_val__1ca063141b6b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:06:06.934274+00:00
-- url     : https://prove2.me/submissions/a3e61a47-4b93-4166-be90-802d5e3cfd65

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_val__of_even_abec3e74f714


set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution [Fact (1 < n)] (ho : Odd n) : s₀ n < val₂ (n - 1) := by
  exact lt_of_le_pred (val₂_of_even (Nat.Odd.sub_odd ho ⟨0, rfl⟩)) (findGreatest_le (val₂ (n - 1) - 1))
end SPP
