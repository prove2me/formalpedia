-- Prove2me | solution 1 for PI.QuotInvW.ae_mem_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:21.149021+00:00
-- url     : https://prove2.me/submissions/50ca3a36-ba59-4aee-af4f-f97569f9a73d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
import Theorems.Thm_PI_QuotInvW_nu_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  rw [ae_iff]
  simpa using nu_compl h
end PI.QuotInvW
