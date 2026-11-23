-- Prove2me | solution 1 for SPP.nonwitnessGroup_of_not_isSquare_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:16:48.743188+00:00
-- url     : https://prove2.me/submissions/6f489ca7-61e7-4824-99cb-5fcea09b5fb4

import Definitions.Def_MillerRabin_StrongProbable
import Definitions.Def_MillerRabin_Miscellaneous
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_P2M_val__of_even_abec3e74f714
import Theorems.Thm_SPP_mem_nonwitnessGroup
import Theorems.Thm_SPP_nonwitnessGroup_le
import Theorems.Thm_SPP_spp_unit_iff
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
open Nat Subgroup
open SPP
namespace SPP
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (hn : ¬IsSquare (-1 : ZMod n)) :
    nonwitnessGroup n = comap (powMonoidHom (oddPart (n - 1))) (closure {-1}) := by
  apply le_antisymm
  · apply nonwitnessGroup_le
    intro a ha
    rw [mem_comap, powMonoidHom_apply, mem_closure_neg_one]
    rw [spp_unit_iff] at ha
    apply ha.imp_right
    intro ⟨s, hs, hs'⟩
    cases s with
    | zero => rwa [Nat.pow_zero, one_mul] at hs'
    | succ s =>
      absurd hn
      use a ^ (2 ^ s * oddPart (n - 1))
      rw [Nat.pow_succ, mul_right_comm, pow_mul, pow_two] at hs'
      norm_cast
      simp [hs']
  · intro a ha
    apply mem_nonwitnessGroup
    rw [mem_comap, powMonoidHom_apply, mem_closure_neg_one] at ha
    rw [spp_unit_iff]
    apply ha.imp_right
    intro ha
    have : NeZero (n - 1) := ⟨by omega⟩
    use 0, val₂_of_even (Nat.Odd.sub_odd ho odd_one)
    simpa
end SPP
