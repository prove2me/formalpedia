-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.retained_energy_of_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:06:35.195913+00:00
-- url     : https://prove2.me/submissions/b603e327-5bf7-4f1a-9df7-472224ef9d6e

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_gram_lower
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27RetainedEnergy_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem solution (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 4 → ℂ) :
    retainedEnergy z ≤ complexGram V (fun i => (gramScales i : ℂ)*z i.succ) := by
  exact retained_gram_lower V hV (fun i => z i.succ)
