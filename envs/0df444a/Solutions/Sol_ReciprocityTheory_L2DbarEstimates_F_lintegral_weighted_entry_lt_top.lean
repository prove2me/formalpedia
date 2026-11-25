-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.lintegral_weighted_entry_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:41.977353+00:00
-- url     : https://prove2.me/submissions/81551e12-f81c-482f-b939-e77b25769381

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sqNorm_entry_le_two_mul
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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (σ : M → Fin n → Fin n → ℂ) (p : M → ℝ) (hσ : n2 n z σ p < ⊤) (j k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖σ x j k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by
  unfold n2 at hσ
  have h2 : ∫⁻ x, ENNReal.ofReal (2 * (sq2 n (σ x) * Real.exp (-p x))) ∂vol n z < ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hσ
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) h2
  apply ENNReal.ofReal_le_ofReal
  have h1 := sqNorm_entry_le_two_mul (σ x) j k
  have he := (Real.exp_pos (-p x)).le
  nlinarith
end ReciprocityTheory.L2DbarEstimates.F
