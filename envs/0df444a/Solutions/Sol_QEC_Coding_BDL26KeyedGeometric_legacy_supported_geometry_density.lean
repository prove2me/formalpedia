-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_supported_geometry_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:27:28.18547+00:00
-- url     : https://prove2.me/submissions/67f6aa2a-b7a6-4959-bb6c-3d2443a3e27d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_positive
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
    ∀ w ∈ geometricSupport P p ∩ geometricAvoidance P J p,
      IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  ⟨keyGood_positive P (triangleKey P) (triangleKey_injective P) J p hJ hv,
    keyGood_geometry_density P (triangleKey P) (triangleKey_injective P) J p hJ hv⟩
end QEC.Coding.BDL26KeyedGeometric
