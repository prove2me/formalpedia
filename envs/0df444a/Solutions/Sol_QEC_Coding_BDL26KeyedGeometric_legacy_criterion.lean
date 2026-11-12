-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:27:14.396813+00:00
-- url     : https://prove2.me/submissions/c17071c6-59d7-49af-bb8b-80e7f6cd568c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_actual_event_criterion
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
    (hv : BoundedValence P) (e : Event P J (anchorRadius p.m)) :
    (geometricLaw P p).real (localEvent (eventSupport P J (anchorRadius p.m))
      (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) :=
  key_actual_event_criterion P (triangleKey P) (triangleKey_injective P) J p hJ hv e
end QEC.Coding.BDL26KeyedGeometric
