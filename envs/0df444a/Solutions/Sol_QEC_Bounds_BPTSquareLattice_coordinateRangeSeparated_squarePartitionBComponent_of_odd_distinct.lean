-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionBComponent_of_odd_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:50:35.2984+00:00
-- url     : https://prove2.me/submissions/448fda96-8bcc-4ace-80e1-3605fb410930

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionBComponent_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_even_cornerCutoutComponents

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (leftIndex rightIndex : Nat × Nat)
    (hoddLeft : ¬ Even (leftIndex.1 + leftIndex.2))
    (hoddRight : ¬ Even (rightIndex.1 + rightIndex.2))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionBComponent blockWidth margin leftIndex)
      (L.squarePartitionBComponent blockWidth margin rightIndex) := by
  have hevenLeft : Even (leftIndex.1 + leftIndex.2 + 1) := by
    rcases Nat.not_even_iff_odd.mp hoddLeft with ⟨half, hhalf⟩
    exact ⟨half + 1, by omega⟩
  have hevenRight : Even (rightIndex.1 + rightIndex.2 + 1) := by
    rcases Nat.not_even_iff_odd.mp hoddRight with ⟨half, hhalf⟩
    exact ⟨half + 1, by omega⟩
  exact coordinateRangeSeparated_of_even_cornerCutoutComponents L hblockWidth hrangeBlock
    hrangeMargin (L.squarePartitionBComponent blockWidth margin)
    (fun _ => Finset.inter_subset_left)
    (fun index site hsite =>
      (L.mem_squarePartitionBComponent_iff blockWidth margin index site |>.mp hsite).2.1)
    1 leftIndex rightIndex hevenLeft hevenRight hne
end QEC.Bounds.BPTSquareLattice
