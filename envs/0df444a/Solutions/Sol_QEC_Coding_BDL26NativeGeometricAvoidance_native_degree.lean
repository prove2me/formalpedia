-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:31:05.072838+00:00
-- url     : https://prove2.me/submissions/841962b4-bc13-4a32-8b3b-6c7d4f4bb755

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_degree_le_of_density
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
    ((supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e).card ≤
      dependencyBound p.M :=
  key_event_degree_le_of_density _ _ (BDL26NativeTriangleColors.nativeKey_injective S n)
    J (anchorRadius p.m) p.M p.t hJ (state_boundedValence S n) p.pool e
end QEC.Coding.BDL26NativeGeometricAvoidance
