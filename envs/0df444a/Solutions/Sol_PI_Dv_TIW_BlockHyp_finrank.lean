-- Prove2me | solution 1 for PI.Dv.TIW.BlockHyp.finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:15.418794+00:00
-- url     : https://prove2.me/submissions/f528b61c-a296-48bf-9bcf-adeed7fb5c5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_mem
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_inj
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
  [IsScalarTower (𝓞 K) K V] {n : ℕ}
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}
namespace PI.Dv.TIW
namespace BlockHyp
theorem _root_.solution [FiniteDimensional K V] (H : BlockHyp X Y Φ Ψ Γ) : Module.finrank K Y = n * Module.finrank K X := by
  let f : (Fin n → X) →ₗ[K] Y := LinearMap.codRestrict Y
    (Φt Φ ∘ₗ LinearMap.pi (fun i => X.subtype ∘ₗ LinearMap.proj i))
    (fun x => H.phi_mem _ (fun i _ => (x i).2))
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
      rw [← sub_eq_zero, ← map_sub] at h
      have := H.phi_inj _ (Submodule.sub_mem _ (fun i _ => (x i).2) (fun i _ => (y i).2)) h
      funext i
      apply Subtype.ext
      have := congrFun this i
      simpa [sub_eq_zero] using this
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := H.h4 y hy
      refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
      apply Subtype.ext
      simp [f, Φt_apply]
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  simp
end BlockHyp
end PI.Dv.TIW
