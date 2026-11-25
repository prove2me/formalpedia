-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:10.960584+00:00
-- url     : https://prove2.me/submissions/ae579923-c060-46d3-bc57-74b802bedb02

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
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
theorem _root_.solution {X P Q : ℝ≥0∞} (hQ : Q ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → X ≤ P + ENNReal.ofReal δ * Q) : X ≤ P := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨q, rfl⟩ : ∃ q : NNReal, Q = q := ⟨Q.toNNReal, (ENNReal.coe_toNNReal hQ).symm⟩
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  set δ : ℝ := min 1 ((ε : ℝ) / ((q : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε' hq1)
  refine (h δ hδpos (min_le_left _ _)).trans (add_le_add le_rfl ?_)
  have hle : δ * q ≤ ε := by
    have h1 : δ ≤ (ε : ℝ) / ((q : ℝ) + 1) := min_le_right _ _
    have h3 : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hq1]
      linarith
    calc δ * q ≤ (ε : ℝ) / ((q : ℝ) + 1) * q := mul_le_mul_of_nonneg_right h1 q.2
      _ = (ε : ℝ) * ((q : ℝ) / ((q : ℝ) + 1)) := by ring
      _ ≤ (ε : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = ε := mul_one _
  calc ENNReal.ofReal δ * (q : ENNReal) = ENNReal.ofReal (δ * q) := by
        rw [ENNReal.ofReal_mul hδpos.le, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hle
    _ = ε := ENNReal.ofReal_coe_nnreal
end ReciprocityTheory.L2DbarEstimates.F
