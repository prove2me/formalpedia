-- Prove2me | solution 1 for ZMod.fst_chineseRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:10:42.616335+00:00
-- url     : https://prove2.me/submissions/310c1db8-d8f1-448c-a5c0-ac4c4b2637cf

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).1 = x.cast := by
  simp [ZMod.chineseRemainder]
end ZMod
