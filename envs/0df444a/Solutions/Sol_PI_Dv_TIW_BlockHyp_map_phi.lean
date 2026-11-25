-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.map_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:17.674141+00:00
-- url     : https://prove2.me/submissions/e6b8f2aa-163b-472b-b68f-fdd388d5d15f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_mem

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
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) :
    (Submodule.pi Set.univ fun _ : Fin n => X).map (Φt Φ) = Y := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact H.phi_mem x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := H.h4 y hy
    exact ⟨x, fun i _ => hx i, by rw [Φt_apply]⟩
end BlockHyp
end PI.Dv.TIW
