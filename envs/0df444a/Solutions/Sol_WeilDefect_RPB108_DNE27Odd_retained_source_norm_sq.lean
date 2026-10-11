-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.retained_source_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:28:56.912454+00:00
-- url     : https://prove2.me/submissions/4c1771c6-7995-4ff0-8bc9-2ca7a9b995b4

import Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
import Theorems.Thm_WeilDefect_RPB108_source_gram_norm_sq
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27SourcePairing_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

namespace WeilDefect.RPB108
/-- Exact column congruence for the retained quadratic form. -/
theorem scaled_retained_gram (V : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ)
    (z : Fin 3 → ℂ) :
    complexGram (fun i j => s i*s j*V i j) z =
      complexGram V (fun i => (s i : ℂ)*z i) := by
  simpa [complexGram] using scaled_gram_difference V (fun _ _ => 0) s 1 z
end WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (source : Fin 4 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    ‖∑ i : Fin 3, z i.succ • source i.succ‖^2 =
      complexGram G (fun i => (gramScales i : ℂ)*z i.succ) := by
  rw [source_gram_norm_sq (fun i => source i.succ)
    (fun i j => gramScales i*gramScales j*G i j) hGram]
  exact scaled_retained_gram G gramScales (fun i => z i.succ)
