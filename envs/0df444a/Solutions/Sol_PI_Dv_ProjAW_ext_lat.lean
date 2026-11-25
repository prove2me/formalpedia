-- Prove2me | solution 1 for PI.Dv.ProjAW.ext_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:06.214795+00:00
-- url     : https://prove2.me/submissions/a75c9bf8-f03e-4812-b990-14025b2e1387

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
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
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.ProjAW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (g : L →ₗ[𝓞 K] K) :
    ∃ φ : V →ₗ[K] K, ∀ a : L, φ a = g a := by
  let S := nonZeroDivisors (𝓞 K)
  have hV : IsLocalizedModule S (LinearMap.id : V →ₗ[𝓞 K] V) := isLocalizedModule_id S V K
  have hK : IsLocalizedModule S (LinearMap.id : K →ₗ[𝓞 K] K) := isLocalizedModule_id S K K
  haveI : IsLocalizedModule S L.subtype :=
    { map_units := fun x => hV.map_units x
      surj := by
        intro y
        have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
        induction hy using Submodule.span_induction with
        | mem x hx => exact ⟨(⟨x, hx⟩, 1), by simp⟩
        | zero => exact ⟨(0, 1), by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨⟨a, s⟩, ha⟩ := hx
          obtain ⟨⟨b, t⟩, hb⟩ := hy
          refine ⟨(t • a + s • b, s * t), ?_⟩
          simp only [Submonoid.smul_def, Submonoid.coe_mul, Submodule.subtype_apply,
            Submodule.coe_add, Submodule.coe_smul] at ha hb ⊢
          rw [← ha, ← hb]
          module
        | smul c x _ hx =>
          obtain ⟨⟨a, s⟩, ha⟩ := hx
          obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj S c
          have key : (q : 𝓞 K) • (c • x) = p • x := by
            rw [← algebraMap_smul K (q : 𝓞 K) (c • x), smul_smul, mul_comm]
            simp only at hpq
            rw [hpq, algebraMap_smul]
          refine ⟨(p • a, q * s), ?_⟩
          simp only [Submonoid.smul_def, Submonoid.coe_mul, Submodule.subtype_apply,
            Submodule.coe_smul] at ha ⊢
          rw [mul_comm, mul_smul, key, smul_comm, ha]
      exists_of_eq := fun {x₁ x₂} h => ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩ }
  refine ⟨(IsLocalizedModule.lift S L.subtype g (fun x => hK.map_units x)).extendScalarsOfIsLocalization
    S K, fun a => ?_⟩
  rw [LinearMap.extendScalarsOfIsLocalization_apply']
  exact IsLocalizedModule.lift_apply S L.subtype g _ a
end PI.Dv.ProjAW
