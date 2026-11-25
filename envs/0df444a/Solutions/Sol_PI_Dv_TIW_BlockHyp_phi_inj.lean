-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.phi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:24.59609+00:00
-- url     : https://prove2.me/submissions/96c7f2a3-bd86-4783-a633-b7683eece413

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psiPhi
import Theorems.Thm_P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c


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
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X)
    (h0 : Φt Φ x = 0) : x = 0 := by
  have := H.psiPhi x hx
  rw [h0, map_zero] at this
  rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]
end BlockHyp
end PI.Dv.TIW
