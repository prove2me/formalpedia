-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:31:20.09314+00:00
-- url     : https://prove2.me/submissions/f3fa17d4-367e-46a4-b0c3-92661f07b82c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_actual_event_criterion
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
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    (geometricLaw (Presentation S n) p).real
      (localEvent (NativeSupport S n J (anchorRadius p.m))
        (NativeBad S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) :=
  key_actual_event_criterion _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J p hJ (state_boundedValence S n) e
end QEC.Coding.BDL26NativeGeometricAvoidance
