-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.psiPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:41.246075+00:00
-- url     : https://prove2.me/submissions/3cb1642b-b2c6-41c1-94d4-ae48b38cb35f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20
import Theorems.Thm_PI_Dv_TIW_matV_apply


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
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}
namespace PI.Dv.TIW
namespace BlockHyp
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    LinearMap.pi Ψ (Φt Φ x) = matV Γ x := by
  funext j
  rw [Ψt_apply, Φt_apply, map_sum, matV_apply]
  exact Finset.sum_congr rfl fun i _ => H.h1 i j (x i) (hx i (Set.mem_univ i))
end BlockHyp
end PI.Dv.TIW
