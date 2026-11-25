-- Prove2me | solution 1 for PI.Dv.IdxW.lenS_ker_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:38.11405+00:00
-- url     : https://prove2.me/submissions/c31c9bbc-9d13-4950-b8e9-5b44e7a18694

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
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
open PI PI.Dv PI.Dv.IdxW
open NumberField IsDedekindDomain Module
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
namespace PI.Dv.IdxW
theorem _root_.solution (S : Submonoid R) {V' : Type*} [AddCommGroup V'] [Module R V']
    (φ : V →ₗ[R] V') (k : Submodule R V) (hk : ∀ x, x ∈ k ↔ φ x = 0) (D X : Submodule R V)
    (hDX : D ≤ X) :
    lenS S X D = lenS S (X ⊓ k) (D ⊓ k) + lenS S (X.map φ) (D.map φ) := by
  let f0 : ↥(X ⊓ k) →ₗ[R] ↥X := Submodule.inclusion inf_le_left
  let g0 : ↥X →ₗ[R] ↥(X.map φ) := φ.submoduleMap X
  let f := Submodule.mapQ ((D ⊓ k).comap (X ⊓ k).subtype) (D.comap X.subtype) f0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, f0, Submodule.coe_inclusion] at hx ⊢
    exact (Submodule.mem_inf.1 hx).1)
  let g := Submodule.mapQ (D.comap X.subtype) ((D.map φ).comap (X.map φ).subtype) g0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at hx ⊢
    exact Submodule.mem_map_of_mem hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, f0, Submodule.coe_inclusion] at ha ⊢
      exact Submodule.mem_inf.2 ⟨ha, (Submodule.mem_inf.1 x.2).2⟩
  have hg : Function.Surjective g := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      simp only [g, Submodule.mapQ_apply]
      congr 1
      ext
      simp [g0, hxy]
  have hex : Function.Exact f g := by
    intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        simp only [g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at h
        obtain ⟨d, hd, hdx⟩ := Submodule.mem_map.1 h
        have hmem : (x : V) - d ∈ X ⊓ k :=
          Submodule.mem_inf.2 ⟨X.sub_mem x.2 (hDX hd), (hk _).2 (by rw [map_sub, hdx, sub_self])⟩
        refine ⟨Submodule.Quotient.mk ⟨(x : V) - d, hmem⟩, ?_⟩
        simp only [f, Submodule.mapQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, f0,
          Submodule.coe_inclusion, sub_sub_cancel_left, neg_mem_iff]
        exact hd
      · rintro ⟨a, ha⟩
        rw [← ha]
        induction a using Submodule.Quotient.induction_on with
        | H z =>
          simp only [f, g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
            Submodule.subtype_apply, f0, g0, LinearMap.submoduleMap_coe_apply, Submodule.coe_inclusion]
          rw [(hk _).1 (Submodule.mem_inf.1 z.2).2]
          exact Submodule.zero_mem _
  unfold lenS
  exact Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
    (LocalizedModule.map_exact S f g hex)
end PI.Dv.IdxW
