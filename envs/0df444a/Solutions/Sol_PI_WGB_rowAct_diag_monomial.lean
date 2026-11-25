-- Prove2me | solution 1 for PI.WGB.rowAct_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:22.931257+00:00
-- url     : https://prove2.me/submissions/31ee2b95-9020-487b-b8e6-917f2828c2bf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_PI_WGB_chiB_weight
import Theorems.Thm_PI_WGB_chiB_wnB
import Theorems.Thm_PI_WGB_rowAct_diag_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution {n N : ℕ} (t : Fin n → ℂ) (e : Fin N × Fin N →₀ ℕ) (c : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (monomial e c) =
      chiB t (Finsupp.weight (wnB n N) e) • monomial e c := by
  have hC : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) (C c) = C c := by
    simp [Formalism.GradedWeylDivisibility.rowAct]
  rw [chiB_weight, monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow, rowAct_diag_X, mul_pow, Finset.prod_mul_distrib, chiB_wnB]
  rw [smul_eq_C_mul, map_prod]
  simp only [C_pow]
  ring
end PI.WGB
