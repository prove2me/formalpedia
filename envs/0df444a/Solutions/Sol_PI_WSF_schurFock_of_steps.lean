-- Prove2me | solution 1 for PI.WSF.schurFock_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:03.335105+00:00
-- url     : https://prove2.me/submissions/428dadb2-0184-4914-9fde-378369c23a11

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_Assembly
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
namespace PI.WSF
theorem _root_.solution (hB : HaarU) (hC : SchurOrth) : PI.SchurFock := by
  intro N lam s hs hbd
  obtain ⟨μ, hμ⟩ := hB N
  have hprob := hμ.1
  have hae := hμ.2.1
  rw [hC N lam μ hμ s hs]
  have hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1 := by
    calc ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)
          filter_upwards [hae] with x hx
          exact pow_le_one₀ (norm_nonneg _) (hbd x hx)
      _ = 1 := by simp
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hint
end PI.WSF
