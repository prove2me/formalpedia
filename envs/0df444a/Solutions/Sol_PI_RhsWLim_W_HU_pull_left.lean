-- Prove2me | solution 1 for PI.RhsWLim.W.HU.pull_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:19.772936+00:00
-- url     : https://prove2.me/submissions/efac41ed-331b-4308-8cde-2e6b4932ec03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
import Theorems.Thm_PI_RhsWLim_W_HU_inc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.HU
theorem _root_.solution (μ : Measure (Mt k r)) (h : ∀ a ∈ UWb k r, μ.map (lmulM a) = μ) :
    (pull μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulM (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun m : Measure (Mt k r) => m (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulM_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mat k r) (Matrix.of x : Mat k r)
        (uwb_unit (inc_mem g))
end PI.RhsWLim.W.HU
