-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_sumList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:28.430637+00:00
-- url     : https://prove2.me/submissions/801136d8-ecd7-48c2-bf28-d020546aea9d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_add

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
    ∀ l : List (Fin d → PowerSeries C), (∀ g ∈ l, IsCurve v g) → IsCurve v (G.sumList l)
  | [], _ => isCurve_zero
  | g :: l, h => isCurve_add G (h g (by simp))
      (solution G l fun g' hg' => h g' (by simp [hg']))
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
