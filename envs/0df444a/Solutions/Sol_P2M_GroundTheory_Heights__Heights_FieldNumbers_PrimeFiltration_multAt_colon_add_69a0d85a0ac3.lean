-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multAt_colon_add_69a0d85a0ac3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:21.474986+00:00
-- url     : https://prove2.me/submissions/33730c0b-4f82-43e5-a00b-1b1138d6c4da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (J W : Ideal (MRing ι F)) [W.IsPrime] (s : MRing ι F) :
    multAt J W = multAt (J.colon (Ideal.span {s})) W + multAt (J ⊔ Ideal.span {s}) W := by
  let f : (MRing ι F ⧸ J.colon (Ideal.span {s})) →ₗ[MRing ι F] (MRing ι F ⧸ J) :=
    Submodule.liftQ _ (J.mkQ ∘ₗ LinearMap.mulRight (MRing ι F) s) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply]
      exact (PrimeFiltration.mem_colon_iff).mp hx)
  let g : (MRing ι F ⧸ J) →ₗ[MRing ι F] (MRing ι F ⧸ (J ⊔ Ideal.span {s})) :=
    Submodule.factor le_sup_left
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply] at hx
    exact (PrimeFiltration.mem_colon_iff).mpr hx
  have hg : Function.Surjective g := Submodule.factor_surjective _
  have hex : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    constructor
    · intro hy
      have hy' : y ∈ J ⊔ Ideal.span {s} := by
        have := hy
        simp only [g] at this
        rwa [← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk t, ?_⟩
      simp only [f, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
        Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem ha
    · rintro ⟨x, hx⟩
      rw [← hx]
      induction x using Submodule.Quotient.induction_on with
      | H t =>
      simp only [f, g, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨t, rfl⟩)
  let p := W.primeCompl
  let R' := Localization.AtPrime W
  let fL := (IsLocalizedModule.map p (LocalizedModule.mkLinearMap p _)
    (LocalizedModule.mkLinearMap p _) f).extendScalarsOfIsLocalization p R'
  let gL := (IsLocalizedModule.map p (LocalizedModule.mkLinearMap p _)
    (LocalizedModule.mkLinearMap p _) g).extendScalarsOfIsLocalization p R'
  exact Module.length_eq_add_of_exact fL gL
    (IsLocalizedModule.map_injective p _ _ f hf) (IsLocalizedModule.map_surjective p _ _ g hg)
    (LocalizedModule.map_exact p f g hex)
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
