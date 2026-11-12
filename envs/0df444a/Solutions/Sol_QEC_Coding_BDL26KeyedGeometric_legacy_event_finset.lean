-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_event_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:20:59.168472+00:00
-- url     : https://prove2.me/submissions/4f2dc27e-8d78-408e-adb8-26d0bba1c483

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
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (legacyEventEquiv P J r e).val = e.val := rfl
end QEC.Coding.BDL26KeyedGeometric
