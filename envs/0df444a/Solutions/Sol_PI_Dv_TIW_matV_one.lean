-- Prove2me | solution 1 for PI.Dv.TIW.matV_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:29.831831+00:00
-- url     : https://prove2.me/submissions/33a8c3e7-4658-4972-bbe6-246c5096a679

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_matV_apply
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] :
    (matV (1 : Matrix n n K) : (n → V) →ₗ[K] (n → V)) = LinearMap.id := by
  apply LinearMap.ext; intro x; funext k
  simp [matV_apply, Matrix.one_apply, ite_smul]
end PI.Dv.TIW
