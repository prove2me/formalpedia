-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.good_of_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:38.24483+00:00
-- url     : https://prove2.me/submissions/a21d7c87-8f02-423a-b82f-0f57dfafdbc2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_one

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {n : Matrix ι ι K} (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    n ∈ Good σ J e f :=
  ⟨n, hn, 1, 1, by rw [map_one, one_mul], by rw [tor_one hσ hJ he hff hef, Matrix.mul_one]⟩
end ReciprocityTheory.ChartRestriction.G.SA
