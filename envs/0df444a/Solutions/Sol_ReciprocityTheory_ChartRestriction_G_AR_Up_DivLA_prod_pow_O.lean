-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.prod_pow_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:27.327802+00:00
-- url     : https://prove2.me/submissions/84913a03-9dcc-4ea2-afe2-f60404edc3bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_mulO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Asymptotics.isBigO_const_const (1 : ℂ) one_ne_zero _
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mulO ((hu a).pow (e a)) ih rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
