-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.inverse_source_pairing_square_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:32:03.019987+00:00
-- url     : https://prove2.me/submissions/53872390-692d-4e57-a515-32b0875780c8

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_source_norm_sq
import Theorems.Thm_WeilDefect_RPB108_inverse_source_pairing_square
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SourcePairing_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108.DNE27Odd
/-- The low source has scale exactly one in the preserved four-column frame. -/
theorem low_source_square_identity : sourceSquare 0 = rawSourceSquare 0 := by
  norm_num [sourceSquare, scales, Matrix.cons_val_two]
end WeilDefect.RPB108.DNE27Odd

theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (source : Fin 4 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hT : ‖T‖ ≤ 1/highFloor) (hsource0 : ‖source 0‖^2 ≤ sourceSquare 0)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    ‖inverseSourcePairing T source z‖^2 ≤ (rawSourceSquare 0/highFloor^2)*
      complexGram G (fun i => (gramScales i : ℂ)*z i.succ) := by
  rw [low_source_square_identity] at hsource0
  have hk : 0 < highFloor := by norm_num [highFloor]
  have h := inverse_source_pairing_square T (source 0)
    (∑ i : Fin 3, z i.succ • source i.succ) (rawSourceSquare 0) highFloor hk hT hsource0
  rw [retained_source_norm_sq source G hGram z] at h
  exact h
