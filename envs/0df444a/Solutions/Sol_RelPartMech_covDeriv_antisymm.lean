-- Prove2me | solution 1 for RelPartMech.covDeriv_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:33:48.832786+00:00
-- url     : https://prove2.me/submissions/59cdff14-198e-4e86-a0ec-3d0ed2690343

import Mathlib
import Definitions.Def_RelPartMech_coordinates
open scoped ContDiff
open RelPartMech

theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (α β : Fin n) (x : Coord n) :
    covDerivCov g A α β x - covDerivCov g A β α x = pd α (A β) x - pd β (A α) x := by
  have hsym : ∀ γ, christoffel g γ β α x = christoffel g γ α β x := by
    intro γ
    unfold christoffel
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    have hs : (fun y => g y β α) = (fun y => g y α β) := funext fun y => hg.2.1 y β α
    simp only [christoffelFirst, hs]
    ring
  simp only [covDerivCov, hsym]
  ring
