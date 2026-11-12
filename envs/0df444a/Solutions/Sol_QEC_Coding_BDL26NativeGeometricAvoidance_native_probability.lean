-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:30:27.500888+00:00
-- url     : https://prove2.me/submissions/3ab44c59-126e-4c28-8f68-94f4a62ca316

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_probability_real_bound
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
    (e : NativeEvent S n J (anchorRadius p.m)) :
    (geometricLaw (Presentation S n) p).real
      (localEvent (NativeSupport S n J (anchorRadius p.m))
        (NativeBad S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) :=
  key_probability_real_bound _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J p e
end QEC.Coding.BDL26NativeGeometricAvoidance
