-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.measurableSet_KeyAvoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:42:38.140119+00:00
-- url     : https://prove2.me/submissions/ef5a7745-03b1-4ad5-a3ed-b808dcf57db9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_avoid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : MeasurableSet (KeyAvoid P key hk J p) := by
  apply measurableSet_avoid
  exact measurableSet_localEvent _ _ (measurableSet_keyBad P key hk J _ _ _)
end QEC.Coding.BDL26KeyedGeometric
