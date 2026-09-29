-- Prove2me | solution 1 for UnitDistanceArcGraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T20:22:39.463756+00:00
-- url     : https://prove2.me/submissions/b6874a4a-647b-4587-a0b9-59c882ed994d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CrossingNumber
import Definitions.Def_unitDist
import Theorems.Thm_UnitDistanceArcSelectionDrawing
import Theorems.Thm_PolygonalReplacementForGeometricArcs

open Classical
open scoped Real
noncomputable section

theorem solution (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ G : SimpleGraph P, ∃ (_ : Fintype G.edgeSet),
      (unitDist P : ℝ) - (P.card : ℝ) ≤ (G.edgeFinset.card : ℝ) ∧
        (CrossingNumber G : ℝ) ≤ 2 * (P.card : ℝ) ^ 2 := by
  rcases UnitDistanceArcSelectionDrawing P with ⟨G, hGfin, D, hedge, hlocal⟩
  letI := hGfin
  rcases PolygonalReplacementForGeometricArcs G D with ⟨_D', _hcard, hcross⟩
  refine ⟨G, hGfin, hedge, ?_⟩
  exact (Nat.cast_le.mpr hcross).trans hlocal
