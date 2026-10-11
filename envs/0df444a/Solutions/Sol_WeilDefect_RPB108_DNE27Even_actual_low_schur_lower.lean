-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.actual_low_schur_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:57:54.433785+00:00
-- url     : https://prove2.me/submissions/60b146d0-937b-468f-aade-77c4b7322bd0

import Theorems.Thm_WeilDefect_RPB108_low_schur_lower_of_norm_bound
import Mathlib
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem low_native_floor_identity :
    lowNativeLower = nativeLow+rawSourceSquare 0/highFloor := by
  norm_num [lowNativeLower, nativeLow, rawSourceSquare, highFloor]
end WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
/-- The low source has scale exactly one in the preserved four-column frame. -/
theorem low_source_square_identity : sourceSquare 0 = rawSourceSquare 0 := by
  norm_num [sourceSquare, scales, Matrix.cons_val_two]
end WeilDefect.RPB108.DNE27Even

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (source : Fin 4 → E) (lowDiag : ℝ)
    (hT : ‖T‖ ≤ 1/highFloor) (hsource0 : ‖source 0‖^2 ≤ sourceSquare 0)
    (hlow : lowNativeLower ≤ lowDiag) : nativeLow ≤ actualLowSchur T source lowDiag := by
  rw [low_source_square_identity] at hsource0
  have hn : nativeLow+rawSourceSquare 0/highFloor ≤ lowDiag := by
    rw [← low_native_floor_identity]
    exact hlow
  exact low_schur_lower_of_norm_bound T (source 0) highFloor (rawSourceSquare 0)
    lowDiag nativeLow (by norm_num [highFloor]) hT hsource0 hn
