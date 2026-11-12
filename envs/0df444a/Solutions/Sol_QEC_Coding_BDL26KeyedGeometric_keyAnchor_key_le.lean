-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyAnchor_key_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:35:58.960244+00:00
-- url     : https://prove2.me/submissions/d10e877d-071a-414f-9f41-4e39f912181f

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
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val) :
    key (keyAnchor P key hk J radius e) ≤ key a := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' key hk
  exact Finset.min'_le _ a ha
end QEC.Coding.BDL26KeyedGeometric
