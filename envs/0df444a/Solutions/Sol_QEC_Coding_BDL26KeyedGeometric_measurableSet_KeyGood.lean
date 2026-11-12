-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.measurableSet_KeyGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:49:30.826192+00:00
-- url     : https://prove2.me/submissions/3acfc56c-487e-49b3-8df7-483b14e6dc58

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_KeyAvoid
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_geometricSupport


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) : MeasurableSet (KeyGood P key hk J p) :=
  (measurableSet_geometricSupport P p).inter (measurableSet_KeyAvoid P key hk J p)
end QEC.Coding.BDL26KeyedGeometric
