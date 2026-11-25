-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.one_le_normSq_jacU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:45.618456+00:00
-- url     : https://prove2.me/submissions/28036844-920a-496b-b03d-177db4ad77f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE

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
theorem _root_.solution {y : UpI ι r → ℂ} (hy : y ∈ Cy ι r) : 1 ≤ Complex.normSq (jacU y) := by
  unfold jacU
  rw [map_prod]
  calc (1 : ℝ) = ∏ _i : Ix ι r, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => ?_
      split_ifs
      · have h1 := ((hy (dI i.1 i.2.2)).1 rfl).1
        rw [Complex.normSq_eq_norm_sq]
        nlinarith
      · simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
