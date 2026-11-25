-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:25.171973+00:00
-- url     : https://prove2.me/submissions/537cc0af-2c68-4027-942f-f66f1c3d9651

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumList

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) :
    ∀ l : List (Fin d → PowerSeries C), (∀ g ∈ l, IsCurve v g) → ∀ a,
      G.lgCurve (G.sumList l) a = (l.map fun g => G.lgCurve g a).sum
  | [], _, a => by simp [LogFGL.sumList, lgCurve_zero]
  | g :: l, h, a => by
      have hl : ∀ g' ∈ l, IsCurve v g' := fun g' hg' => h g' (by simp [hg'])
      rw [LogFGL.sumList, lgCurve_add G (fun b => (h g (by simp) b).1)
        (fun b => (isCurve_sumList G l hl b).1), solution G l hl a]
      simp
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
