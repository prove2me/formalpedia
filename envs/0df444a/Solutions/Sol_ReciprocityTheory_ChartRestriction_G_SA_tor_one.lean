-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:53.839849+00:00
-- url     : https://prove2.me/submissions/3a60e96e-5649-4c85-8a78-49978349f6fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet

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
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution : tor σ J e f 1 1 = 1 := by
  simp [tor]
end ReciprocityTheory.ChartRestriction.G.SA
