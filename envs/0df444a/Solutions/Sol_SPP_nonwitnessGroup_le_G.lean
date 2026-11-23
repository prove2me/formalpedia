-- Prove2me | solution 1 for SPP.nonwitnessGroup_le_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:14:27.395339+00:00
-- url     : https://prove2.me/submissions/fd9b183a-4d9b-48c8-a844-2409c3b527dd

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_nonwitnessGroup_le
import Theorems.Thm_SPP_spp_unit_iff
import Theorems.Thm_P2M_SPP_le_s__81aa0fe3ef1b
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution :
    nonwitnessGroup n ≤ G n := by
  apply nonwitnessGroup_le
  intro a ha
  rw [G, mem_comap, powMonoidHom_apply]
  rcases spp_unit_iff.mp ha with ha | ⟨s, hs, ha⟩
  · rw [mul_comm, pow_mul]
    simp [ha]
  · rw [← Nat.add_sub_cancel' (le_s₀ hs ha), pow_add, mul_right_comm, pow_mul, ha,
      mem_closure_singleton]
    use 2 ^ (s₀ n - s)
    norm_cast
end SPP
