-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:21:33.429692+00:00
-- url     : https://prove2.me/submissions/93f6403c-cf65-49b2-a8a9-0978de2d8a0e

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
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (g : Grid K) :
    keyCenter P (triangleKey P) (triangleKey_injective P) J r l K e g =
      eventCenter P J r l K (legacyEventEquiv P J r e) g := rfl
end QEC.Coding.BDL26KeyedGeometric
