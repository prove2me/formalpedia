-- Prove2me | solution 1 for QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_cover
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:49:04.460193+00:00
-- url     : https://prove2.me/submissions/ad8555f6-e18c-4510-b96a-3e9a6736d376

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_self

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) :
    (embedding.gridOccupiedCells w origin).biUnion
      (embedding.gridCellQubits w origin) = Finset.univ := by
  ext q
  constructor
  · intro _
    simp
  · intro _
    refine Finset.mem_biUnion.mpr ⟨gridCellIndex w origin (embedding.point q), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    · exact embedding.mem_gridCellQubits_self w origin q
