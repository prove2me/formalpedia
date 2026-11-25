-- Prove2me | solution 1 for PI.GTNum.top_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:09.218184+00:00
-- url     : https://prove2.me/submissions/707c7136-689f-4fc3-9bb8-12b52ff2bdfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_GTCoefTopMain
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
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
namespace PI.GTNum
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (hn : 0 < n) (lam lam' : DomWeight N) (sg : DomWeight n)
    (hag : ∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i)
    (htop : lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩)
    (htop' : lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩) :
    cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg := by
  have hD0 : D0 h lam' sg = D0 h lam sg := by
    unfold D0
    exact Finset.sum_congr rfl (fun i _ => by rw [hag _ (Nat.succ_ne_zero _)])
  have h1 : lam'.w ⟨1, by omega⟩ = lam.w ⟨1, by omega⟩ := hag _ (Nat.succ_ne_zero _)
  have key : ∀ i : Fin n,
      min (lam'.w ⟨i.1, by omega⟩) (lam'.w ⟨i.1 + 1, by omega⟩ + D0 h lam' sg) =
        min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg) ∧
      lam'.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨i.1 + 1, by omega⟩ ∧
      min (lam'.w ⟨i.1, by omega⟩ - lam'.w ⟨i.1 + 1, by omega⟩) (D0 h lam' sg) =
        min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg) := by
    intro i
    have e1 : lam'.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨i.1 + 1, by omega⟩ := hag _ (Nat.succ_ne_zero _)
    by_cases hi : i.1 = 0
    · have a0 : lam'.w ⟨i.1, by omega⟩ = lam'.w ⟨0, by omega⟩ := congrArg lam'.w (Fin.ext hi)
      have b0 : lam.w ⟨i.1, by omega⟩ = lam.w ⟨0, by omega⟩ := congrArg lam.w (Fin.ext hi)
      have b1 : lam.w ⟨i.1 + 1, by omega⟩ = lam.w ⟨1, by omega⟩ :=
        congrArg lam.w (Fin.ext (by simp [hi]))
      refine ⟨?_, e1, ?_⟩ <;> omega
    · have e0 : lam'.w ⟨i.1, by omega⟩ = lam.w ⟨i.1, by omega⟩ := hag _ hi
      rw [e0, e1, hD0]
      exact ⟨rfl, rfl, rfl⟩
  have hR : ∀ i : Fin n, Rset h lam' sg i = Rset h lam sg i := by
    intro i
    unfold Rset
    rw [(key i).1, (key i).2.1]
  constructor
  · unfold cBr
    exact Finset.prod_congr rfl (fun i _ => by rw [hR i])
  · unfold D1
    exact Finset.sum_congr rfl (fun i _ => (key i).2.2)
end PI.GTNum
