-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:05.349054+00:00
-- url     : https://prove2.me/submissions/6551133c-e96c-4068-a124-7757460a279d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (δ : ℝ≥0∞) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ' : ℝ≥0∞, 0 < δ' ∧ ∀ a b : ℝ≥0∞, a < δ' → b < δ' → ENNReal.ofReal C * (a + b) < δ := by
  rcases eq_or_ne δ ⊤ with rfl | hδt
  · refine ⟨1, one_pos, fun a b ha hb => ?_⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ha.trans ENNReal.one_lt_top, hb.trans ENNReal.one_lt_top⟩)
  have hr0 : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  have hC1 : 0 < C + 1 := by linarith
  have hq : 0 < δ.toReal / (2 * (C + 1)) := div_pos hr0 (by linarith)
  refine ⟨ENNReal.ofReal (δ.toReal / (2 * (C + 1))), ENNReal.ofReal_pos.2 hq, fun a b ha hb => ?_⟩
  have hat : a ≠ ⊤ := (ha.trans ENNReal.ofReal_lt_top).ne
  have hbt : b ≠ ⊤ := (hb.trans ENNReal.ofReal_lt_top).ne
  have ha' : a.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hb' : b.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hbt ENNReal.ofReal_ne_top).2 hb
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hs : 0 ≤ a.toReal + b.toReal := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hlt : C * (a.toReal + b.toReal) < δ.toReal := by
    have h1 : C * (a.toReal + b.toReal) ≤ (C + 1) * (a.toReal + b.toReal) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    have h2 : (C + 1) * (a.toReal + b.toReal) < (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) :=
      mul_lt_mul_of_pos_left (by linarith) hC1
    have h3 : (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) = δ.toReal := by
      field_simp
    linarith
  calc ENNReal.ofReal C * (a + b) = ENNReal.ofReal (C * (a.toReal + b.toReal)) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hbt]
    _ < ENNReal.ofReal δ.toReal := (ENNReal.ofReal_lt_ofReal_iff hr0).2 hlt
    _ = δ := ENNReal.ofReal_toReal hδt
end ReciprocityTheory.L2DbarEstimates.F
