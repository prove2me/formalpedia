-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hAngle_sin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:18:01.691761+00:00
-- url     : https://prove2.me/submissions/7879ed99-506a-4252-be3e-b5f1d07609d4

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : Real.sin hAngle = Real.sqrt 7 / 4 := by
  rw [hAngle, Real.sin_arccos]
  have hroot : Real.sqrt (1 - ((3 : Real) / 4) ^ 2) = Real.sqrt 7 / 4 := by
    rw [show 1 - ((3 : Real) / 4) ^ 2 = 7 / 16 by norm_num]
    rw [Real.sqrt_div (by norm_num : 0 ≤ (7 : Real))]
    norm_num
  exact hroot
end QEC.Distillation.OneQubitMagic
