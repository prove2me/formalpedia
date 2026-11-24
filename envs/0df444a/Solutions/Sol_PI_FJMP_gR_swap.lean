-- Prove2me | solution 1 for PI.FJMP.gR_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:31.3601+00:00
-- url     : https://prove2.me/submissions/37b21a93-6839-4131-ab30-5cdc695f84f4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
variable {κ : Type*} [Fintype κ]
namespace PI.FJMP
theorem _root_.solution (u v : κ → σ) (pos : κ → Bool) (P : MvPolynomial σ ℂ) :
    gR v u (fun c => !pos c) P = -gR u v pos P := by
  unfold gR
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases Bool.eq_false_or_eq_true (pos c) with h | h <;> simp [h]
end PI.FJMP
