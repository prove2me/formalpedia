-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.grid_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:26:45.261201+00:00
-- url     : https://prove2.me/submissions/df430f53-6989-45b1-be89-ebbf11fb996b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (b : Fin 2) :
    grid S large k b (Fin.last S.half)=armVertex S large k b := by
  have last_eq : Fin.last S.half = (⟨S.half, by omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  have height_eq : height S large k =
      (⟨(sliceIndex S large k).val+1, by
        have := (sliceIndex S large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid armVertex
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [last_eq,height_eq]
  exact subdivisionGridVertex_edgeInterior_qz0 Seed center S (oldFace b)
    (sliceIndex S large k)
end QEC.Coding.BDL26FirstReplacementSparseExactness
