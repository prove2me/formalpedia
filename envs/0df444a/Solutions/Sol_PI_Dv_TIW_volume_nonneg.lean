-- Prove2me | solution 1 for PI.Dv.TIW.volume_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:58.658802+00:00
-- url     : https://prove2.me/submissions/d71a7585-f4c8-4a78-baf2-ab380a6bff76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h
end PI.Dv.TIW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega
end PI.Dv.TIW
