-- Prove2me | solution 1 for RelPartMech.gSymbol_eq_christoffel_diff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:33:42.276984+00:00
-- url     : https://prove2.me/submissions/03e2521c-74f0-45ce-a6ed-53e58da5e7b5

import Mathlib
import Definitions.Def_RelPartMech_coordinates
open scoped ContDiff
open RelPartMech

theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    gSymbol g α β γ x = christoffelFirst g β α γ x - christoffelFirst g α β γ x := by
  have hs : (fun y => g y β α) = (fun y => g y α β) := funext fun y => hg.2.1 y β α
  simp only [gSymbol, christoffelFirst, hs]
  ring
