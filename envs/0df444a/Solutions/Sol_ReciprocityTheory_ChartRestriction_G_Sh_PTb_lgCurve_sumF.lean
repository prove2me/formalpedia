-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:56.402994+00:00
-- url     : https://prove2.me/submissions/3c7f4501-7fac-4851-ac3f-f474d17cc78c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sumList

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
    (h : ∀ u, IsCurve v (g u)) (a : Fin d) :
    G.lgCurve (G.sumF g) a = ∑ u, G.lgCurve (g u) a := by
  rw [show G.sumF g = G.sumList (List.ofFn g) from rfl,
    lgCurve_sumList G _ (fun g' hg' => by
      obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hg'
      exact h u) a]
  simp [List.map_ofFn, List.sum_ofFn]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
