-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalArenaTemplate.pointer_gives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:56:59.325774+00:00
-- url     : https://prove2.me/submissions/fff758e3-9541-4e52-a3aa-308bfa26c483

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_region_space
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalArenaTemplate
theorem _root_.solution {lim : Limits} {loc : ℕ → ℤ} {free C : ℕ} (hfree : loc 1 = (free : ℤ)) (hC : loc 24 = (C : ℤ))
    (hpos : 1 ≤ C) (hw : (lim.space : ℤ) ≤ lim.word) (hend : finish free C ≤ lim.space) (slot : ℕ) (hs : slot < 67)
    (μ : ℕ → ℤ) : (ptrExpr slot).Gives lim ⟨loc, μ⟩ (addr free C slot : ℕ) :=
  by
  have hs' : slot < slots := hs
  have ha : addr free C slot ≤ lim.space := region_space (len := 0) hs' (by omega) hend
  have hprod : slot * C ≤ lim.space := by unfold addr at ha; omega
  have hslot : slot ≤ lim.space := by nlinarith
  have hprodInt : (slot : ℤ) * (C : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hprod).trans hw
  have hprodNonneg : 0 ≤ (slot : ℤ) * (C : ℤ) := by positivity
  have haddrInt : (free : ℤ) + (slot : ℤ) * (C : ℤ) ≤ lim.word := by exact_mod_cast (Int.ofNat_le.mpr ha).trans hw
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ptrExpr, hfree, hC, addr] <;> omega)
end ThreeSum.LightWeightedGlobalArenaTemplate
