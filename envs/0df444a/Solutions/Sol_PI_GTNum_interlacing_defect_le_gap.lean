-- Prove2me | solution 1 for PI.GTNum.interlacing_defect_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:27.95182+00:00
-- url     : https://prove2.me/submissions/87f5c4b1-61cc-4d88-8d87-ef52ae19dd65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_GTNum_sum_range_le_tele
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
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
namespace PI.GTNum
theorem _root_.solution (hI : Interlace h lam sg) (hn : 0 < n) :
    D0 h lam sg ≤ sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩ := by
  let t : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ else lam.w ⟨N - 1, by omega⟩
  let a : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ - lam.w ⟨k + 1, by omega⟩ else 0
  have hD : D0 h lam sg = ∑ k ∈ range n, a k := by
    unfold D0
    rw [← Fin.sum_univ_eq_sum_range a n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [a, dif_pos i.2]
  have ht0 : t 0 = sg.w ⟨0, hn⟩ := by simp only [t, dif_pos hn]
  have htn : t n = lam.w ⟨N - 1, by omega⟩ := by simp only [t, dif_neg (lt_irrefl n)]
  rw [hD, ← ht0, ← htn]
  refine sum_range_le_tele n a t (fun k hk => ?_)
  simp only [a, t, dif_pos hk]
  by_cases hk1 : k + 1 < n
  · rw [dif_pos hk1]
    have := (hI ⟨k + 1, hk1⟩).1
    have e : lam.w ⟨(⟨k + 1, hk1⟩ : Fin n).1, by omega⟩ = lam.w ⟨k + 1, by omega⟩ := rfl
    omega
  · rw [dif_neg hk1]
    have e : lam.w ⟨k + 1, by omega⟩ = lam.w ⟨N - 1, by omega⟩ := congrArg lam.w (Fin.ext (by simp; omega))
    omega
end PI.GTNum
