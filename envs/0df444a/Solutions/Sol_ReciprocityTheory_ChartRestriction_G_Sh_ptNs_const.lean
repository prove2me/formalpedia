-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptNs_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:02.598426+00:00
-- url     : https://prove2.me/submissions/1bc2c45c-f7d7-4b98-9ecf-cf01a826563d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves

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
theorem _root_.solution (G : LogFGL v d) : ∀ n a, constantCoeff (ptNs G n a) = 0
  | 0, a => by simp [ptNs]
  | n + 1, a => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact solution G n i
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (G.F_const a)
end ReciprocityTheory.ChartRestriction.G.Sh
