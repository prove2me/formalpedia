-- Prove2me | solution 1 for P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:12.83395+00:00
-- url     : https://prove2.me/submissions/4fdcb8e2-7b4c-4268-a0a9-babbc37b8497

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_snd_comp_chineseRemainder__e253f5662d04
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder


attribute [local simp] ZMod.fst_chineseRemainderₓ
attribute [local simp] ZMod.unitsMap_chineseRemainderₓ_symm
attribute [local simp] ZMod.snd_chineseRemainderₓ

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_left n m)) ((chineseRemainderₓ h).symm (x, y)) = y := by
  rw [← snd_comp_chineseRemainderₓ h]; simp
end ZMod
