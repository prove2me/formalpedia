-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptc_elim_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:57.103671+00:00
-- url     : https://prove2.me/submissions/8a4f0964-a2eb-4bac-ab47-583abce51af1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood

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
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) :
    ∀ s, constantCoeff (Sum.elim x y s) = 0 := by
  intro s
  cases s with
  | inl s => exact hx s
  | inr s => exact hy s
end ReciprocityTheory.ChartRestriction.G.Sh
