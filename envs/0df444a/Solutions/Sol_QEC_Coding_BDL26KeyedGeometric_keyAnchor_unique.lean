-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyAnchor_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:44:22.130169+00:00
-- url     : https://prove2.me/submissions/de9d4392-d42f-4477-bdb6-a472ab858eb9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_mem
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_key_le

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
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val)
    (hmin : ∀ b ∈ e.val, key a ≤ key b) : keyAnchor P key hk J radius e = a := by
  apply hk
  exact Nat.le_antisymm (keyAnchor_key_le P key hk J radius e a ha)
    (hmin _ (keyAnchor_mem P key hk J radius e))
end QEC.Coding.BDL26KeyedGeometric
