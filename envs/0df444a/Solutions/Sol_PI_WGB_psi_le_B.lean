-- Prove2me | solution 1 for PI.WGB.psi_le_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:14.260065+00:00
-- url     : https://prove2.me/submissions/c370b15a-81ca-4a83-a64c-d7ac79f1929b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
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
theorem _root_.solution {n N : ℕ} (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e ≤ n * Finsupp.weight (1 : Fin N × Fin N → ℕ) e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  have : psiB n N v ≤ n := by
    unfold psiB prowB
    split_ifs <;> omega
  calc e v * psiB n N v ≤ e v * n := Nat.mul_le_mul_left _ this
    _ = n * e v := mul_comm _ _
end PI.WGB
