-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyAnchor_proof_irrel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:15:59.115248+00:00
-- url     : https://prove2.me/submissions/4e24b938-6d95-489b-933e-5dca855c6e6b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk hk' : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    keyAnchor P key hk J radius e = keyAnchor P key hk' J radius e := rfl
end QEC.Coding.BDL26KeyedGeometric
