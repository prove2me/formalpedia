-- Prove2me | solution 1 for P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:18.178998+00:00
-- url     : https://prove2.me/submissions/6895852d-c97d-4792-b1d2-85bc4418dba5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}
namespace PI.Dv.TIW
theorem _root_.solution (Ψ : Fin n → V →ₗ[K] V) (y : V) (j : Fin n) : (LinearMap.pi Ψ) y j = Ψ j y := rfl
end PI.Dv.TIW
