-- Prove2me | solution 1 for PI.HookSteps.Cap.detD_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:33.793795+00:00
-- url     : https://prove2.me/submissions/09b1e2d1-f5e5-447b-95e2-c512f54ac459

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
import Theorems.Thm_PI_HookSteps_Cap_dop_comm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution (N : ℕ) : detD N = ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤˣ) : ℤ) •
    dw (dop N) (id : Fin N → Fin N) (fun j => π j) := by
  unfold detD
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  unfold dw
  have hp := Equiv.Perm.ofFn_comp_perm σ⁻¹ (fun j => dop N j (σ j))
  have hc : (List.ofFn ((fun j => dop N j (σ j)) ∘ ⇑σ⁻¹)).Pairwise Commute :=
    List.pairwise_ofFn.mpr fun i j _ => dop_comm N _ _ _ _
  refine Eq.trans ?_ ((hp.prod_eq' hc).trans rfl)
  congr 1
  congr 1
  funext j
  simp [dop]
end PI.HookSteps.Cap
