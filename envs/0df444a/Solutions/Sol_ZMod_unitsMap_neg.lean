-- Prove2me | solution 1 for ZMod.unitsMap_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:46.009815+00:00
-- url     : https://prove2.me/submissions/5a82ca46-7f95-4301-ab92-815a55e55314

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder


attribute [local simp] ZMod.fst_chineseRemainderₓ
attribute [local simp] ZMod.unitsMap_chineseRemainderₓ_symm
attribute [local simp] ZMod.snd_chineseRemainderₓ
attribute [local simp] ZMod.unitsMap_chineseRemainderₓ_symm'

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {n m : ℕ} (hm : n ∣ m) (x : (ZMod m)ˣ) :
    unitsMap hm (-x) = -unitsMap hm x := by
  simp [unitsMap_def]
end ZMod
