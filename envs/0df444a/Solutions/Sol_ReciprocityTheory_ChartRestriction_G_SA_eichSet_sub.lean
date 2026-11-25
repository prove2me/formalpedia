-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eichSet_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:08.452909+00:00
-- url     : https://prove2.me/submissions/8e158427-906f-4c7c-8257-02a4a5fc0c8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub

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
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : eichSet σ J e f ⊆ SU σ J :=
  Set.union_subset (eichAlong_sub hσ hJ he) (eichAlong_sub hσ hJ hff)
end ReciprocityTheory.ChartRestriction.G.SA
