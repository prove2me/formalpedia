-- Prove2me | solution 1 for P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:52.815702+00:00
-- url     : https://prove2.me/submissions/be3793c2-9c6c-4cd4-8570-cb796f1bd72e

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder


attribute [local simp] ZMod.fst_chineseRemainderₓ
attribute [local simp] ZMod.unitsMap_chineseRemainderₓ_symm

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).2 = unitsMap (dvd_mul_left n m) x :=
  Units.ext (snd_chineseRemainder h)
end ZMod
