-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_bad_predicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:23:49.950703+00:00
-- url     : https://prove2.me/submissions/7e7ed0f5-a1e3-4b5a-b90a-bb0b398a82b4

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
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (legacyAssignmentEquiv P J r e) ⁻¹'
      eventBad P J r l K (legacyEventEquiv P J r e) =
      keyBad P (triangleKey P) (triangleKey_injective P) J r l K e := rfl
end QEC.Coding.BDL26KeyedGeometric
