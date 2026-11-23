-- Prove2me | solution 1 for P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:17.699695+00:00
-- url     : https://prove2.me/submissions/2a13718d-b408-4bed-912d-aa1fd70d71bd

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder


attribute [local simp] ZMod.fst_chineseRemainderₓ

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_right m n)) ((chineseRemainderₓ h).symm (x, y)) = x := by
  rw [← fst_comp_chineseRemainderₓ h]; simp
end ZMod
