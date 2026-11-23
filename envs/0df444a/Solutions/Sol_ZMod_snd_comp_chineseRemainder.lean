-- Prove2me | solution 1 for ZMod.snd_comp_chineseRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:53.013669+00:00
-- url     : https://prove2.me/submissions/7e1a856f-3fa5-4cb8-89f8-f772d6878620

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} (h : m.Coprime n) :
    (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) :=
  RingHom.ext fun _ ↦ snd_chineseRemainder h
end ZMod
