-- Prove2me | solution 1 for PI.WeylForKWork.weyl_formula_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:58.391165+00:00
-- url     : https://prove2.me/submissions/6cb7ab3a-e43c-48f0-88ac-7819e7b91b10

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_prod_split
import Theorems.Thm_PI_WeylForKWork_rhoC_ePl
import Theorems.Thm_PI_WeylForKWork_rhoC_eMi
import Theorems.Thm_PI_WeylForKWork_prod_pairs_split
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
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution : FormulaStep := by
  intro N ε Λ
  have hsp := prod_pairs_split ε (fun a b => (Λ + rhoC ε) a - (Λ + rhoC ε) b)
  rw [hsp, wu, wu, mul_div_mul_comm]
  congr 2
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, rhoC_ePl]
    ring
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, rhoC_eMi]
    ring
end PI.WeylForKWork
