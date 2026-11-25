-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_length_quot_smul_top_eq_c98b42d6d7fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:28.26915+00:00
-- url     : https://prove2.me/submissions/a243d1ce-02cb-4bef-8778-57165dd9451a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.LocalSectionLengthSum
namespace GroundTheory.Heights₂.Heights.LocalSectionLengthSum
theorem _root_.solution {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]
end GroundTheory.Heights₂.Heights.LocalSectionLengthSum
