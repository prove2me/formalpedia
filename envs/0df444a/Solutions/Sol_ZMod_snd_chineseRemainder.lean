-- Prove2me | solution 1 for ZMod.snd_chineseRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:10.247815+00:00
-- url     : https://prove2.me/submissions/b3ba251f-5138-4da9-b9fa-ab9f3f66a84e

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Theorems.Thm_ZMod_fst_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).2 = x.cast := by
  simp [ZMod.chineseRemainder]
end ZMod
