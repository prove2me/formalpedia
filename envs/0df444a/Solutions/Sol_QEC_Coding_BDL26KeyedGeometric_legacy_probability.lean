-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:26:57.972212+00:00
-- url     : https://prove2.me/submissions/b48d5ba0-e93c-426d-b70a-5945e7186d03

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_probability_real_bound
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
    {L : ℝ} (p : GeometricParameters L) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      probabilityCoefficient (6*p.m) (capCutoff p.m)/(p.lambda : ℝ) :=
  key_probability_real_bound P (triangleKey P) (triangleKey_injective P) J p e
end QEC.Coding.BDL26KeyedGeometric
