-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.actual_retained_schur_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:58:33.817536+00:00
-- url     : https://prove2.me/submissions/55214dd0-93c0-4151-aa50-d7731f3afcb5

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_source_norm_sq
import Theorems.Thm_WeilDefect_RPB108_complex_gram_add_div
import Theorems.Thm_WeilDefect_RPB108_inverse_quadratic_upper
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (source : Fin 4 → E)
    (V G : Fin 3 → Fin 3 → ℝ) (hT : ‖T‖ ≤ 1/highFloor)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    complexGram V (fun i => (gramScales i : ℂ)*z i.succ) ≤
      actualRetainedSchur T source V G z := by
  have hu := inverse_quadratic_upper T (∑ i : Fin 3, z i.succ • source i.succ) highFloor hT
  rw [retained_source_norm_sq source G hGram z] at hu
  unfold actualRetainedSchur retainedNativeEnergy
  rw [complex_gram_add_div]
  linarith
