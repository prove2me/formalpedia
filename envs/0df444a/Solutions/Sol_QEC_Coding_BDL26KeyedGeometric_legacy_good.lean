-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:26:54.678419+00:00
-- url     : https://prove2.me/submissions/18f6ab0a-a0fc-4440-ab33-1fcd31fd7215

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
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
    {L : ℝ} (p : GeometricParameters L) :
    KeyGood P (triangleKey P) (triangleKey_injective P) J p =
      geometricSupport P p ∩ geometricAvoidance P J p := rfl
end QEC.Coding.BDL26KeyedGeometric
