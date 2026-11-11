-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.measurableSet_keyBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:34:05.70689+00:00
-- url     : https://prove2.me/submissions/fcfa66ef-d6c0-4981-a2a9-6c6260f47959

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_triangleHit


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
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) :
    MeasurableSet (keyBad P key hk J radius lambda K e) := by
  apply MeasurableSet.iUnion
  intro g
  apply MeasurableSet.iInter
  intro a
  exact (measurableSet_triangleHit _ _ _).preimage (by fun_prop)
end QEC.Coding.BDL26KeyedGeometric
