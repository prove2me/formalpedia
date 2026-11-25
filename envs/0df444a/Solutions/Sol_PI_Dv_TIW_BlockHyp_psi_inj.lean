-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.psi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:22.478887+00:00
-- url     : https://prove2.me/submissions/bae576c6-4e7b-4fdc-b141-e65e7d069887

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
import Theorems.Thm_PI_Dv_TIW_BlockHyp_psiPhi
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c
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
  [IsScalarTower (𝓞 K) K V] {n : ℕ}
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}
namespace PI.Dv.TIW
namespace BlockHyp
theorem _root_.solution (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) (h0 : LinearMap.pi Ψ y = 0) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := H.h4 y hy
  have hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun i _ => hx i
  have := H.psiPhi x hx'
  rw [Φt_apply] at this
  rw [h0] at this
  have hx0 : x = 0 := by rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]
  simp [hx0]
end BlockHyp
end PI.Dv.TIW
