-- Prove2me | solution 1 for RobustUncLP.WorstCase.robustFeas_subset_instFeas
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:33:09.646849+00:00
-- url     : https://prove2.me/submissions/944bd161-6e8f-482c-a9bc-34a333938256

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

open RobustUncLP.WorstCase in
theorem solution {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) :
    ∀ A ∈ U, robustFeas U f ⊆ instFeas f A := by
  intro A hA x hx
  exact ⟨hx.1 A hA, hx.2⟩
