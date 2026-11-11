-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.grid_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:40:07.612816+00:00
-- url     : https://prove2.me/submissions/3c94e740-1f37-473e-98ca-74e923eecdc1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (b : Fin 2) :
    grid S n large k b (Fin.last S.half)=armVertex S n large k b := by
  have last_eq : Fin.last S.half = (⟨S.half, by omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  have height_eq : height S n large k =
      (⟨(sliceIndex S n large k).val+1, by
        have := (sliceIndex S n large k).isLt; omega⟩ : Fin (S.half+1)) := by
    apply Fin.ext
    rfl
  unfold grid armVertex
  apply congrArg (fun v : SubdivisionVertex Seed center S =>
    (⟨center,(0,v)⟩ : RX0 Seed S))
  rw [last_eq,height_eq]
  exact subdivisionGridVertex_edgeInterior_qz0 Seed center S (oldFace b)
    (sliceIndex S n large k)
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
