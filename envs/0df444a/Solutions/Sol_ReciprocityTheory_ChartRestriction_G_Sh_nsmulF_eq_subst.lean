-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.nsmulF_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:47.50339+00:00
-- url     : https://prove2.me/submissions/93649022-1990-4133-a8ca-00abee31fb65

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_hasSubst

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
theorem _root_.solution (G : LogFGL v d) {ga : Fin d → PowerSeries C}
    (hga : HasSubst ga) : ∀ n, G.nsmulF n ga = fun a => subst ga (ptNs G n a)
  | 0 => by
    funext a
    simp only [LogFGL.nsmulF, ptNs, Pi.zero_apply]
    rw [← substAlgHom_apply hga, map_zero]
  | n + 1 => by
    funext a
    simp only [LogFGL.nsmulF, LogFGL.add, ptNs]
    rw [subst_comp_subst_apply (ptNs_hasSubst G n) hga, solution G hga n]
    congr 1
    funext i
    rcases i with i | i
    · simp [subst_X hga]
    · rfl
end ReciprocityTheory.ChartRestriction.G.Sh
