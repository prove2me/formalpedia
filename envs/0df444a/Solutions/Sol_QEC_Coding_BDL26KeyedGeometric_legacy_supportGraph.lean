-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_supportGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:51:22.316196+00:00
-- url     : https://prove2.me/submissions/1df30169-0abf-4237-8047-2ad656df301a

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
    (r : ℝ) (e f : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (supportGraph (keySupport P (triangleKey P) (triangleKey_injective P) J r)).Adj e f ↔
      (supportGraph (eventSupport P J r)).Adj
        (legacyEventEquiv P J r e) (legacyEventEquiv P J r f) := Iff.rfl
end QEC.Coding.BDL26KeyedGeometric
