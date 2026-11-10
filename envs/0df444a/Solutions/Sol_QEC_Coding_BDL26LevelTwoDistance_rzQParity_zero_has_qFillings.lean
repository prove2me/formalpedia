-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_has_qFillings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:29:30.279658+00:00
-- url     : https://prove2.me/submissions/5a73cdb5-1029-458a-9953-fae6bc0bbbd0

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qTransposeDoubleCylinderBoundary_range_eq_totalParity_ker


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RZQ P S))
    (hparity : rzQParity P S word = 0) :
    ∀ q : P.Q, ∃ edges : Word Field (QDoubleCylinderEdge (transposePresentation P) q S),
      qDoubleCylinderBoundary1 (transposePresentation P) q S edges =
        fun vertex => word (Sum.inr ⟨q, vertex⟩) := by
  intro q
  have hker : (fun vertex : QDoubleCylinderVertex (transposePresentation P) q S =>
      word (Sum.inr ⟨q, vertex⟩)) ∈ LinearMap.ker totalParity := by
    apply LinearMap.mem_ker.mpr
    exact congrFun hparity q
  rw [← qTransposeDoubleCylinderBoundary_range_eq_totalParity_ker P A q S] at hker
  exact hker
end QEC.Coding.BDL26LevelTwoDistance
