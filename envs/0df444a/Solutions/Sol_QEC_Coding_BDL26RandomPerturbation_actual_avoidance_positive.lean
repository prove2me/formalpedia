-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.actual_avoidance_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:13:37.333243+00:00
-- url     : https://prove2.me/submissions/9cade085-15af-47bf-a896-318904bef2d8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_event_criterion
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_localLemma


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))).real
      (avoid (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ) := by
  have hc := capCutoff_bounds p.m_two
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) hc.2 v
  have h := product_localLemma
    (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
    (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (measurableSet_eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
    (fun _ => lllWeight (dependencyBound p.M))
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).1.le)
    (fun _ => (lllWeight_bounds (dependencyBound p.M)).2.2)
    (actual_event_criterion P J p hJ hv)
  exact h.2.1 Finset.univ
end QEC.Coding.BDL26RandomPerturbation
