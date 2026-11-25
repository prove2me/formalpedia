-- Prove2me | solution 1 for PI.LocFramePrimWork.Dual_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:28.034176+00:00
-- url     : https://prove2.me/submissions/ccaedc87-4022-482d-b340-5fc13f4eb277

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist
import Theorems.Thm_PI_LocFramePrimWork_Dual_coe_injective
import Theorems.Thm_PI_LocFramePrimWork_Dual_smul_coe
import Theorems.Thm_PI_LocFramePrimWork_Dual_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (Lb : Submodule (𝓞 E) (Fin n → E)) (hfg : Lb.FG) (z : Fin n → E) (hz : z ∈ Lb)
    (hprim : ∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ ψ : Lb →ₗ[𝓞 E] 𝓞 E, ψ ⟨z, hz⟩ = 1 := by
  classical
  have hz0 : z ≠ 0 := Dual_ne_zero Lb z hprim
  have : Module.IsTorsionFree (𝓞 E) Lb := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r l hrl => ?_
    have h := congrArg Subtype.val hrl
    rw [Submodule.coe_smul, Dual_smul_coe, Submodule.coe_zero, smul_eq_zero] at h
    rcases h with h | h
    · left
      exact Dual_coe_injective (by rw [h]; rfl)
    · right
      exact Subtype.ext h
  have hz0' : (⟨z, hz⟩ : Lb) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  set N : Submodule (𝓞 E) Lb := Submodule.span (𝓞 E) {⟨z, hz⟩} with hN
  have : Module.IsTorsionFree (𝓞 E) (Lb ⧸ N) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q hrq => ?_
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_span_singleton] at hrq
    obtain ⟨a, ha⟩ := hrq
    have hrE : (r : E) ≠ 0 := fun h => hr (Dual_coe_injective (by rw [h]; rfl))
    have hV : ((a : E) / (r : E)) • z = (l : Fin n → E) := by
      have h := congrArg Subtype.val ha
      rw [Submodule.coe_smul, Submodule.coe_smul, Dual_smul_coe, Dual_smul_coe] at h
      rw [div_eq_inv_mul, mul_smul, h, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    obtain ⟨o, ho⟩ := hprim _ (hV ▸ l.2)
    rw [Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_span_singleton]
    refine ⟨o, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, Dual_smul_coe, ho, hV]
  have : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) (Lb ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Lb ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hmem : ∀ l : Lb, l - s (N.mkQ l) ∈ N := by
    intro l
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have h := LinearMap.congr_fun hs (N.mkQ l)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    change N.mkQ l - N.mkQ (s (N.mkQ l)) = 0
    rw [h, sub_self]
  let ρ : Lb →ₗ[𝓞 E] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N hmem
  refine ⟨(LinearEquiv.coord (𝓞 E) Lb ⟨z, hz⟩ hz0').toLinearMap ∘ₗ ρ, ?_⟩
  have hρ : ρ ⟨z, hz⟩ = ⟨⟨z, hz⟩, Submodule.mem_span_singleton_self _⟩ := by
    apply Subtype.ext
    change (⟨z, hz⟩ : Lb) - s (N.mkQ ⟨z, hz⟩) = ⟨z, hz⟩
    rw [(Submodule.mkQ_apply N _).trans ((Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_span_singleton_self _)),
      map_zero, sub_zero]
  rw [LinearMap.comp_apply, hρ]
  exact LinearEquiv.coord_self (𝓞 E) Lb ⟨z, hz⟩ hz0'
end PI.LocFramePrimWork
