-- Prove2me | solution 1 for QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:49:03.52786+00:00
-- url     : https://prove2.me/submissions/93e934a9-3979-4ea5-8d03-e8a9dae7d0e1

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ) :
    (↑(embedding.gridOccupiedCells w origin) : Set (ℤ × ℤ)).PairwiseDisjoint
      (embedding.gridCellQubits w origin) := by
  intro first hfirst second hsecond hne
  apply Finset.disjoint_left.mpr
  intro q hqFirst hqSecond
  have hFirst : gridCellIndex w origin (embedding.point q) = first :=
    (embedding.mem_gridCellQubits_iff w origin first q).1 hqFirst
  have hSecond : gridCellIndex w origin (embedding.point q) = second :=
    (embedding.mem_gridCellQubits_iff w origin second q).1 hqSecond
  exact hne (hFirst.symm.trans hSecond)
