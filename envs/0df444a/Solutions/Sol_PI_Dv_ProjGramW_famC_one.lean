-- Prove2me | solution 1 for PI.Dv.ProjGramW.famC_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.204158+00:00
-- url     : https://prove2.me/submissions/dbbced60-a61b-4d41-9212-24bf5175e85b

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V) :
    famC b (1 : Matrix (Fin d) (Fin d) K) = b := by
  funext j
  simp [famC, Matrix.one_apply]
end PI.Dv.ProjGramW
