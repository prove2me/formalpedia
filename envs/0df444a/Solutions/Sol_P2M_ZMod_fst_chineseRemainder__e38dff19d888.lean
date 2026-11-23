-- Prove2me | solution 1 for P2M_ZMod_fst_chineseRemainder__e38dff19d888
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:10.970581+00:00
-- url     : https://prove2.me/submissions/6beba06e-8183-45d4-8145-4bb6f6c0e2cf

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Theorems.Thm_ZMod_fst_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder



set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).1 = unitsMap (dvd_mul_right m n) x :=
  Units.ext (fst_chineseRemainder h)
end ZMod
