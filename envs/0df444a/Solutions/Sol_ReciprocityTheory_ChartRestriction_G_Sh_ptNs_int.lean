-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptNs_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:11.121079+00:00
-- url     : https://prove2.me/submissions/c5f34e7f-0b37-444a-989e-b6038cedf7f2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIntSer_subst


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
theorem _root_.solution (G : LogFGL v d) : ∀ n a, ptNs G n a ∈ ptIntSer v (Fin d)
  | 0, a => by simp only [ptNs, Pi.zero_apply]; exact Subring.zero_mem _
  | n + 1, a => by
    refine ptIntSer_subst (ptNs_hasSubst G n) ?_ (G.F_int a)
    rintro (i | i)
    · exact ptIntSer_X i
    · exact solution G n i
end ReciprocityTheory.ChartRestriction.G.Sh
