-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyAnchor_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:51:49.170305+00:00
-- url     : https://prove2.me/submissions/d99d8889-cfb7-4c88-8e17-11911237c7ca

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
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) : keyAnchor P key hk J radius e ∈ e.val := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact Finset.min'_mem e.val (keyEvent_nonempty P key hk J radius e)
end QEC.Coding.BDL26KeyedGeometric
