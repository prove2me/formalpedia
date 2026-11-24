-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.measurableSet_sS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:50.640804+00:00
-- url     : https://prove2.me/submissions/beb21614-ee5c-4293-92b5-b3a3c67ad0ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : MeasurableSet (sS ι r) := by
  unfold sS
  have h : {w : Ix ι r → ℂ | ∀ (τ : ι) (b : Fin r), w (τ, b, b) ≠ 0} =
      ⋂ τ : ι, ⋂ b : Fin r, (fun w : Ix ι r → ℂ => w (τ, b, b)) ⁻¹' {0}ᶜ := by
    ext w
    simp
  rw [h]
  exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b =>
    measurable_pi_apply _ (measurableSet_singleton 0).compl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
