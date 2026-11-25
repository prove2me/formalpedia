-- Prove2me | solution 1 for PI.WHw.bC_dualWeyl_le_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:03.026455+00:00
-- url     : https://prove2.me/submissions/9be21c00-bfa4-4b93-bf7e-5da796ae00cf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
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
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
namespace PI.WHw
theorem _root_.solution (r n : ℕ) (ν : Fin n → ℕ) :
    dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
  intro f hf
  have hw : IsWeightedHomogeneous (colW r n) f ν := hf.1
  rw [mem_homogeneousSubmodule]
  intro m hm
  rw [← hw hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one, Finset.sum_apply,
    Pi.smul_apply, colW, Pi.single_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => by simp)
end PI.WHw
