-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_hK_of_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:37.632594+00:00
-- url     : https://prove2.me/submissions/82a36113-0176-4d9c-955f-d8c77f0d5d9e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ τ : Type*} {K : MvPowerSeries σ R}
    (hK : ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α K = 0) (A A' : σ → MvPowerSeries τ R) :
    ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s := by
  intro α hα
  left
  by_contra h
  exact hα (hK α (by omega))
end ReciprocityTheory.ChartRestriction.G.Sh
