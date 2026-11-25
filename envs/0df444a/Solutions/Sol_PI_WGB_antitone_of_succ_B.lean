-- Prove2me | solution 1 for PI.WGB.antitone_of_succ_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:12:58.618833+00:00
-- url     : https://prove2.me/submissions/56907041-eb2b-4fb6-bcfb-b2a570436d6f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n : ℕ} (m : Fin n → ℕ)
    (hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩) : Antitone m := by
  let M : ℕ → ℕ := fun k => if hk : k < n then m ⟨k, hk⟩ else 0
  have hM : Antitone M := by
    refine antitone_nat_of_succ_le fun k => ?_
    by_cases hk1 : k + 1 < n
    · simp only [M, dif_pos hk1, dif_pos (show k < n by omega)]
      exact hdom k hk1
    · simp only [M, dif_neg hk1]
      exact Nat.zero_le _
  intro a b hab
  have := hM (Fin.le_def.mp hab)
  simp only [M, dif_pos a.2, dif_pos b.2] at this
  exact this
end PI.WGB
