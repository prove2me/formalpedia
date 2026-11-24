-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hf_fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:26.616886+00:00
-- url     : https://prove2.me/submissions/46da9566-4611-4065-8076-30d3ccc0c8da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm


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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → R} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
include he hff
variable (hef : hf σ J e f = 1)
include hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : hf σ J f e = 1 := by
  rw [← hf_symm (hσ := hσ) (hJ := hJ) (x := e) (y := f), hef, map_one]
end ReciprocityTheory.ChartRestriction.G.SA
