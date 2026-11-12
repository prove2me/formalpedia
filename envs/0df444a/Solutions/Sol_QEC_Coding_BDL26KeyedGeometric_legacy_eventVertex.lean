-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_eventVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:22:19.029878+00:00
-- url     : https://prove2.me/submissions/daad5d72-c4e4-47e8-b48d-14441b683aee

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
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (a : e.val) (i : Fin 3) :
    legacySupportEquiv P J r e (keyVertex P (triangleKey P) (triangleKey_injective P) J r e a i) =
      eventVertex P J r (legacyEventEquiv P J r e) ⟨a.val,a.property⟩ i := rfl
end QEC.Coding.BDL26KeyedGeometric
