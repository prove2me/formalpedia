-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyEvents_have_dependency_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:35:55.792209+00:00
-- url     : https://prove2.me/submissions/02abf4c2-296c-4ef0-b2b0-081a8ea3ca30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_hasDependencyGraph


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
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K))
      (supportGraph (keySupport P key hk J radius)) := by
  classical
  exact product_hasDependencyGraph ν (keySupport P key hk J radius)
    (keyBad P key hk J radius lambda K) (measurableSet_keyBad P key hk J radius lambda K)
end QEC.Coding.BDL26KeyedGeometric
