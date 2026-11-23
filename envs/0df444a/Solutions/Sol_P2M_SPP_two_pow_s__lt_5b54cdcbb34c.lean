-- Prove2me | solution 1 for P2M_SPP_two_pow_s__lt_5b54cdcbb34c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:14:24.094592+00:00
-- url     : https://prove2.me/submissions/77f88dba-cac9-4d46-bcb0-12ec0b42c058

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_SPP_s__lt_val__1ca063141b6b
import Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74
import Theorems.Thm_oddPart_pos


set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution [Fact (1 < n)] (ho : Odd n) : 2 ^ s₀ n * oddPart (n - 1) < n - 1 := by
  conv_rhs => rw [← two_pow_val₂_mul_oddPart (n - 1)]
  gcongr
  · exact oddPart_pos
  · decide
  · exact s₀_lt_val₂ ho
end SPP
