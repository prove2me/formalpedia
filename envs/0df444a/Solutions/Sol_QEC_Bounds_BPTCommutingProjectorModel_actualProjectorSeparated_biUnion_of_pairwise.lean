-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_biUnion_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:28:47.432727+00:00
-- url     : https://prove2.me/submissions/87f19aa7-1a99-44a3-9eed-041d885eabd2

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (block : Finset L.Site)
    (blocks : Finset (Finset L.Site)) (hblock : block ∉ blocks)
    (hseparated : ∀ other ∈ blocks, block ≠ other →
      M.ActualProjectorSeparated block other) :
    M.ActualProjectorSeparated block (blocks.biUnion id) := by
  intro check hboth
  rcases hboth.2 with ⟨site, hsite⟩
  rcases Finset.mem_inter.mp hsite with ⟨hsupport, hblocks⟩
  rcases Finset.mem_biUnion.mp hblocks with ⟨other, hother, hsiteOther⟩
  apply hseparated other hother
  · intro hsame
    exact hblock (hsame ▸ hother)
  · constructor
    · exact hboth.1
    · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, hsiteOther⟩⟩
end QEC.Bounds.BPTCommutingProjectorModel
