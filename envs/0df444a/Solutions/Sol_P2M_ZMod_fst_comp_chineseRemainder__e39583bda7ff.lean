-- Prove2me | solution 1 for P2M_ZMod_fst_comp_chineseRemainder__e39583bda7ff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:41.036489+00:00
-- url     : https://prove2.me/submissions/3958cc63-2009-4590-8780-95ef80492d60

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder


attribute [local simp] ZMod.fst_chineseRemainderₓ

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.fst (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      unitsMap (dvd_mul_right m n) := by ext; simp
end ZMod
