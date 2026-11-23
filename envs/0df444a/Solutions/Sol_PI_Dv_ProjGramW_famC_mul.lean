-- Prove2me | solution 1 for PI.Dv.ProjGramW.famC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:21.571104+00:00
-- url     : https://prove2.me/submissions/e6e1d9ac-2c6a-42b5-a5ea-93ac6cf26213

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
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
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.ProjGramW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C C' : Matrix (Fin d) (Fin d) K) : famC (famC b C) C' = famC b (C * C') := by
  funext j
  simp only [famC, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end PI.Dv.ProjGramW
