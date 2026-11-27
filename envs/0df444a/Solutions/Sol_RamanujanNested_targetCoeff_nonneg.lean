-- Prove2me | solution 1 for RamanujanNested.targetCoeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T05:06:13.36054+00:00
-- url     : https://prove2.me/submissions/75f72593-f73c-40b0-9a8c-1fa623734467

module
public import Definitions.Def_RamanujanNested_Bounds
public import Mathlib
public import Definitions.Def_RamanujanNested_TargetRadical

set_option autoImplicit true
@[expose] public section
open RamanujanNested
namespace RamanujanNested
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) : 0 ≤ targetCoeff t := by
  unfold targetCoeff
  rw [sub_nonneg, div_le_iff₀ (lt_of_lt_of_le one_pos ht)]
  nlinarith
end RamanujanNested
