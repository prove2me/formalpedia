-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_exists_geometry_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:31:23.361203+00:00
-- url     : https://prove2.me/submissions/af376d07-e72b-430b-b16d-e7f76cd906aa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_exists_keyGood_geometry_density
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
    ∃ w : Vertex (Presentation S n) → Space, w ∈ NativeGood S n J p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound :=
  exists_keyGood_geometry_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J p hJ (state_boundedValence S n)
end QEC.Coding.BDL26NativeGeometricAvoidance
