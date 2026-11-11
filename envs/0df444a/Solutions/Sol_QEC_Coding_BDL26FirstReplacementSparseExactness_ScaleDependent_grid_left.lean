-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.grid_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:40:28.748665+00:00
-- url     : https://prove2.me/submissions/818c82bd-e40d-4837-97ce-8bc0f3981e32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_shared_edge
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) :
    grid S n large k b 0=grid S n large k 0 0 := by
  have height_eq : height S n large k =
      (⟨(sliceIndex S n large k).val+1, by
        have := (sliceIndex S n large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [height_eq]
  exact (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace b)
    (sliceIndex S n large k)).trans
      ((congrArg (fun e : XStarEdge Seed center =>
        (Sum.inr (Sum.inl (e,sliceIndex S n large k)) : SubdivisionVertex Seed center S))
        (shared_edge b)).trans
          (subdivisionGridVertex_edgeInterior_xq1 Seed center S (oldFace 0)
            (sliceIndex S n large k)).symm)
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
