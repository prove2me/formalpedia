-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.foldr_mem
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:56:01.153786+00:00
-- url     : https://prove2.me/submissions/fbe0b6f2-73c7-484d-a793-1a30482dd4a5

import Mathlib
variable {X W : Type}


theorem solution {S : Set (X → ℂ)} {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (l : List W) {Θ : X → ℂ}
    (h : Θ ∈ S) : l.foldr dd Θ ∈ S := by
  induction l with
  | nil => exact h
  | cons w l ih => exact hd w _ ih
