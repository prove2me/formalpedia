-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometricExecution.execution_geometry_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:19:00.817326+00:00
-- url     : https://prove2.me/submissions/5547736f-9c1b-465e-b568-7c0ed23c13c3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_measurable_result
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_halts_good_ae
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26KeyedGeometricExecution
theorem _root_.solution (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    Measurable (result P k hk J p) ∧
    ∀ᵐ T ∂tableMeasure P p,
      Halts (keySupport P k hk J (anchorRadius p.m))
        (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      result P k hk J p T ∈ KeyGood P k hk J p ∧
      IncomingFaceGeometry P (perturbationOddScale p)
        (perturbedMap P J p.lambda (result P k hk J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (result P k hk J p T)))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨measurable_result P k hk J p, ?_⟩
  filter_upwards [halts_good_ae P k hk J p hJ hv] with T hT
  exact ⟨hT.1, hT.2, keyGood_geometry_density P k hk J p hJ hv _ hT.2⟩
end QEC.Coding.BDL26KeyedGeometricExecution
