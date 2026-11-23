-- Prove2me | solution 1 for ZMod.fst_comp_chineseRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:52.340681+00:00
-- url     : https://prove2.me/submissions/366edb8e-72f3-40d6-918b-ecb5892021ea

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Theorems.Thm_ZMod_fst_chineseRemainder
attribute [local simp] ZMod.fst_chineseRemainder

set_option autoImplicit false
open ZMod
namespace ZMod
theorem _root_.solution {m n : ℕ} (h : m.Coprime n) :
    (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) :=
  RingHom.ext fun _ ↦ fst_chineseRemainder h
end ZMod
