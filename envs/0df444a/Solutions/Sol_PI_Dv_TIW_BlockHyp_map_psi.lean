-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.map_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:54.351031+00:00
-- url     : https://prove2.me/submissions/b8f8bd5b-9720-48bc-a319-09736372879e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psiPhi
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_mem
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psi_mem
import Theorems.Thm_PI_Dv_TIW_matV_apply
import Theorems.Thm_PI_Dv_TIW_matV_inv_cancel


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
    Y.map (LinearMap.pi Ψ) = Submodule.pi Set.univ fun _ : Fin n => X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact H.psi_mem y hy
  · intro x hx
    have hx' : matV Γ⁻¹ x ∈ Submodule.pi Set.univ fun _ : Fin n => X := by
      intro k _
      rw [matV_apply]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
    refine ⟨Φt Φ (matV Γ⁻¹ x), H.phi_mem _ hx', ?_⟩
    rw [H.psiPhi _ hx', matV_inv_cancel Γ H.det]
end BlockHyp
end PI.Dv.TIW
