-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_sumF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:20.037002+00:00
-- url     : https://prove2.me/submissions/99b998fb-746f-462f-b3c9-35002f93d33c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
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
theorem _root_.solution (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ u, IsCurve v (g u)) : IsCurve v (G.sumF g) :=
  isCurve_sumList G (List.ofFn g) (fun g' hg' => by
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hg'
    exact h u)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
