-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_supported_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:58:09.358516+00:00
-- url     : https://prove2.me/submissions/6e560f2d-bca6-46c4-99af-8215bcca85d6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_positive
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_KeyGood
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricAvoidance
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26FiniteAlternatingCore BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26NativeGeometricAvoidance
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    MeasurableSet (NativeGood S n J p) ∧
    0 < (geometricLaw (Presentation S n) p).real (NativeGood S n J p) ∧
    ∀ w ∈ NativeGood S n J p,
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  ⟨measurableSet_KeyGood _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p,
    keyGood_positive _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p hJ (state_boundedValence S n),
    keyGood_geometry_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p hJ (state_boundedValence S n)⟩
end QEC.Coding.BDL26NativeGeometricAvoidance
