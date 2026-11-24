-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.one_mem_SU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:04.242666+00:00
-- url     : https://prove2.me/submissions/8a89b576-e09e-4dd4-aa28-f2d112faf1ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : (1 : Matrix ι ι R) ∈ SU σ J := by
  exact ⟨det_one, by simp⟩
end ReciprocityTheory.ChartRestriction.G.SA
