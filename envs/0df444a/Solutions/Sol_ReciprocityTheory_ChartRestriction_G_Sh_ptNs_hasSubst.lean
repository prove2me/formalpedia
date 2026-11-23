-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptNs_hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:55:36.373826+00:00
-- url     : https://prove2.me/submissions/7163c1e4-5fe0-4ea3-b82f-40fff6e5ebb0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_const

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
theorem _root_.solution (G : LogFGL v d) (n : ℕ) :
    HasSubst (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C)) (ptNs G n)) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    cases i with
    | inl b => simp
    | inr b => exact ptNs_const G n b
end ReciprocityTheory.ChartRestriction.G.Sh
