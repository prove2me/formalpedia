-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.key_actual_avoidance_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:24:14.345465+00:00
-- url     : https://prove2.me/submissions/8584251e-b1e0-4e9a-85b8-954ed278dd82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_actual_event_criterion
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_localLemma


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
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (keySupport P key hk J (anchorRadius p.m))
        (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by
  have hc := capCutoff_bounds p.m_two
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) hc.2 v
  have h := product_localLemma
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (keySupport P key hk J (anchorRadius p.m))
    (keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (measurableSet_keyBad P key hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).1.le)
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).2.2)
    (key_actual_event_criterion P key hk J p hJ hv)
  exact h.2.1 Finset.univ
end QEC.Coding.BDL26KeyedGeometric
