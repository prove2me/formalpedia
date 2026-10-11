-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.retained_energy_of_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:05:58.487493+00:00
-- url     : https://prove2.me/submissions/74082ec3-0d57-4ded-a78c-e68aaa8ae99e

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_gram_lower
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem solution (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 4 → ℂ) :
    retainedEnergy z ≤ complexGram V (fun i => (gramScales i : ℂ)*z i.succ) := by
  exact retained_gram_lower V hV (fun i => z i.succ)
