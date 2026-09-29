-- Prove2me | solution 1 for PlaneTreeOneFace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:23:27.851378+00:00
-- url     : https://prove2.me/submissions/27fb7ce2-d0e8-422c-8e92-01e24e2b19ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement
import Theorems.Thm_PlaneTreeDrawingComplementConnected
import Theorems.Thm_OrdinaryDrawingImageCompact
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

 theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.IsTree → @Fintype.card A.Face A.faceFintype = 1 := by
  intro hTree
  exact PlaneFaceDataOneFaceOfPolygonallyPathConnectedComplement G D A
    (PlaneTreeDrawingComplementConnected G D hD hTree)
    (by
      rcases (OrdinaryDrawingImageCompact G D).isBounded.exists_norm_le with ⟨R, hR⟩
      let p : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (max R 0 + 1)
      refine ⟨p, ?_⟩
      intro hp
      have hp_norm_le : ‖p‖ ≤ R := hR p hp
      have hp_norm : ‖p‖ = max R 0 + 1 := by
        have hnonneg : 0 ≤ max R 0 + 1 := by
          nlinarith [le_max_right R 0]
        simp [p, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hR_lt : R < max R 0 + 1 := by
        nlinarith [le_max_left R 0]
      nlinarith)
