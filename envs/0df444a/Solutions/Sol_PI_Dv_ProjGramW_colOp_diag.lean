-- Prove2me | solution 1 for PI.Dv.ProjGramW.colOp_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:41.630028+00:00
-- url     : https://prove2.me/submissions/7e10ae8d-8b3e-4c82-981f-e46eed61c08a

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (k : Fin d) (c : K) :
    colOp k (fun i => if i = k then c else 0) = Matrix.diagonal (fun m => if m = k then c else 1) := by
  ext p q
  simp only [colOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hq : q = k
  · subst hq
    by_cases hp : p = q
    · subst hp; simp
    · simp [hp]
  · by_cases hp : p = q
    · subst hp; simp [hq]
    · simp [hp, hq]
end PI.Dv.ProjGramW
