-- Prove2me | solution 1 for PI.WGB.weight_tau_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:27.773966+00:00
-- url     : https://prove2.me/submissions/0a45cc42-7de2-46a0-8e5f-5c69c4f0723b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RenameTauHomogB
import Theorems.Thm_PI_WGB_wnB_tau
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
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (u : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (wnB n N) (Finsupp.mapDomain (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) u) =
      fun j => Finsupp.weight (wnB n N) u (σ j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • wnB n N i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext j
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, wnB_tau h σ hσ]
end PI.WGB
