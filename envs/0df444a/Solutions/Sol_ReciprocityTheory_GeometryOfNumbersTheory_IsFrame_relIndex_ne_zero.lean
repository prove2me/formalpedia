-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:06.394544+00:00
-- url     : https://prove2.me/submissions/daed3d66-1ac7-4c05-b701-a5eb608f2280

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_span_frame_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace IsFrame
theorem _root_.solution {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  exact hv.relIndex_span_frame_ne_zero hE
end IsFrame
end ReciprocityTheory.GeometryOfNumbersTheory
