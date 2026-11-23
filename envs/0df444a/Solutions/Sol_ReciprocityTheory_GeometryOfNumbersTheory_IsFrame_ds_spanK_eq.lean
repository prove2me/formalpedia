-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.ds_spanK_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:27.955803+00:00
-- url     : https://prove2.me/submissions/3fac6f6c-4ad2-4e83-9060-cd1f1c396efd

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA

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
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace IsFrame
theorem _root_.solution {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  · exact Submodule.span_le.mpr hv.2.2
end IsFrame
end ReciprocityTheory.GeometryOfNumbersTheory
