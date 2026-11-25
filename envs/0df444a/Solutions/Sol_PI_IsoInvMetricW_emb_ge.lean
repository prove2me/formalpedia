-- Prove2me | solution 1 for PI.IsoInvMetricW.emb_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:46.602842+00:00
-- url     : https://prove2.me/submissions/7806bd98-39df-485c-829a-9e2486ed0b80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution {h N : ℕ} (J : Fin h ↪o Fin N) (i : Fin h) : (i : ℕ) ≤ J i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hi⟩ := J.lt_iff_lt.mpr (by simp [Fin.lt_def])
    have h3 : ((J ⟨n, by omega⟩ : Fin N) : ℕ) < ((J ⟨n + 1, hi⟩ : Fin N) : ℕ) := h2
    simp only at h1 ⊢
    omega
end PI.IsoInvMetricW
