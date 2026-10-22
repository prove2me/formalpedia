-- Prove2me | solution 1 for PerishShip.Waste.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:15:24.644651+00:00
-- url     : https://prove2.me/submissions/a1d2cfa8-3ca0-4cbf-a3ef-18591364bcca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PerishShip_Waste_Model
import Theorems.Thm_PerishShip_Waste_theorem_1_warehouse
import Theorems.Thm_PerishShip_Waste_theorem_1_total

open PerishShip.Waste

theorem solution (P : Params) (hP : P.Standing) :
    (∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
      avgUpper (fun s q _ => ww hP.1 s q) (stationary sofFull) s₀ ≤
        avgLower (fun s q _ => ww hP.1 s q) σ s₀) ∧
    (∃ f : State P → Vec P,
      (∀ s, s.Feasible → ShipFeasible s (f s) ∧ IsSOF s (f s)) ∧
      ∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
        avgUpper (wtot hP.1) (stationary f) s₀ ≤
          avgLower (wtot hP.1) σ s₀) :=
  ⟨theorem_1_warehouse P hP, theorem_1_total P hP⟩
