-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.supR_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:32.288886+00:00
-- url     : https://prove2.me/submissions/60522425-4887-4692-87f4-bcaa82e2bf79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC

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
    (hcW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≠ ⊤ := by
  unfold supR
  apply ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne'))
  refine iSup_le fun z => iSup_le fun _ => iSup_le fun hz => ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hW := hcW _ hz
  rw [ENNReal.ofReal_mul hc.le] at hW
  have he : ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heT : ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) ≠ ⊤ := ENNReal.ofReal_ne_top
  set e := ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))
  calc e / W (cpt X x z) ≤ e / (ENNReal.ofReal c * e) := ENNReal.div_le_div_left hW _
    _ = 1 * e / (ENNReal.ofReal c * e) := by rw [one_mul]
    _ = 1 / ENNReal.ofReal c := ENNReal.mul_div_mul_right _ _ he heT
    _ = (ENNReal.ofReal c)⁻¹ := one_div _
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
