-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.uwr_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:20.37741+00:00
-- url     : https://prove2.me/submissions/b83d29c9-84e1-46f8-8026-15031ef61d17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_uwr_amgm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_isFiniteMeasureOnCompacts


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
theorem _root_.solution (hz : IsLocalHomeomorph z) (u h : M → ℂ) (p : M → ℝ) (hp : Continuous p)
    (hu : AEStronglyMeasurable u (vol n z))
    (hfin : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun x => u x * h x) (vol n z) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hcont : Continuous (fun x => ‖h x‖ ^ 2 * Real.exp (p x)) :=
    (hh.norm.pow 2).mul (Real.continuous_exp.comp hp)
  have hcs : HasCompactSupport (fun x => ‖h x‖ ^ 2 * Real.exp (p x)) :=
    (hc.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)).mul_right
  have hI := hcont.integrable_of_hasCompactSupport (μ := vol n z) hcs
  have h2 : ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (p x)) ∂vol n z < ⊤ :=
    hI.lintegral_lt_top
  refine ⟨hu.mul hh.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖u x * h x‖ₑ ∂vol n z < ⊤
  calc ∫⁻ x, ‖u x * h x‖ₑ ∂vol n z
      ≤ ∫⁻ x, (ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-p x)) +
          ENNReal.ofReal (‖h x‖ ^ 2 * Real.exp (p x))) ∂vol n z := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_add (by positivity) (by positivity), norm_mul]
        exact ENNReal.ofReal_le_ofReal (uwr_amgm ‖u x‖ ‖h x‖ (p x))
    _ = _ := lintegral_add_right' _ hcont.measurable.ennreal_ofReal.aemeasurable
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfin, h2⟩
end ReciprocityTheory.L2DbarEstimates.F
