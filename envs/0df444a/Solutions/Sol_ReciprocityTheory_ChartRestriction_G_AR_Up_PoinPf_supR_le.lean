-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.supR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:18.070807+00:00
-- url     : https://prove2.me/submissions/903243e8-6166-4a4a-8fb0-956b7d6d43ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≤ ENNReal.ofReal (1 / c) ^ (1 / 2 : ℝ) := by
  unfold supR
  refine iSup₂_le fun z _ => iSup_le fun hz => ENNReal.rpow_le_rpow ?_ (by norm_num)
  have he : 0 < Real.exp (-phla X la (cpt X x z)) := Real.exp_pos _
  calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)
      ≤ ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) /
          ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x z))) := ENNReal.div_le_div_left (hW _ hz) _
    _ = ENNReal.ofReal (1 / c) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
