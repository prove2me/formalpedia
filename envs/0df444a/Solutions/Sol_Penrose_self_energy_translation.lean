-- Prove2me | solution 1 for Penrose.self_energy_translation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:45:40.561707+00:00
-- url     : https://prove2.me/submissions/f2860d21-3b64-4b7d-beca-a2dd9b293b2d

import Mathlib
import Definitions.Def_penrose
import Definitions.Def_penrose_energy

open MeasureTheory
open Penrose

theorem solution (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (h : ∀ x, ⇑ρ' x = ⇑ρ (x - v)) :
    gravSelfEnergy G ρ = gravSelfEnergy G ρ' := by
  unfold gravSelfEnergy
  congr 1
  simp_rw [h]
  conv_rhs => rw [← integral_add_right_eq_self _ v]
  congr 1; funext x
  conv_rhs => rw [← integral_add_right_eq_self _ v]
  congr 1; funext y
  simp only [add_sub_cancel_right]
  congr 2
  abel_nf

