-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_dependency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:27:47.930057+00:00
-- url     : https://prove2.me/submissions/22253ab3-e0b5-4f2b-90b0-8291af983288

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvents_have_dependency_graph
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
    (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν) (localEvent (NativeSupport S n J r) (NativeBad S n J r l K))
      (supportGraph (NativeSupport S n J r)) :=
  keyEvents_have_dependency_graph _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r l K ν
end QEC.Coding.BDL26NativeGeometricAvoidance
