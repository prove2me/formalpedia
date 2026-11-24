-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepLength_proof_86d6f2aa590e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:56.367165+00:00
-- url     : https://prove2.me/submissions/eb62b640-fa04-434c-ac0a-80db647d259b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FiltrationStepLength
theorem _root_.solution : FiltrationStepLength.Statement := by
  intro R _ K ι L W _ f
  let g₁ : (MRing ι R ⧸ L.colon {f}) →ₗ[MRing ι R] MRing ι R ⧸ L :=
    Submodule.mapQ _ _ (LinearMap.mulRight (MRing ι R) f) (fun x hx => by
      have := Submodule.mem_colon_singleton.mp hx
      simpa [smul_eq_mul] using this)
  let g₂ : (MRing ι R ⧸ L) →ₗ[MRing ι R] MRing ι R ⧸ (L ⊔ Ideal.span {f}) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => Submodule.mem_sup_left hx)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | _ c => ?_
    rw [LinearMap.mem_ker] at hy
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_colon_singleton.mpr (by simpa [smul_eq_mul] using hy)
  have hsurj : Function.Surjective g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply]
      rw [Submodule.Quotient.eq]
      have e : c * f - (l + c * f) = -l := by ring
      rw [e]
      exact L.neg_mem hl
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulRight_apply] at hx
      rw [Submodule.Quotient.eq] at hx
      have e : a = -(c * f - a) + c * f := by ring
      rw [e]
      exact Submodule.add_mem_sup (L.neg_mem hx) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have key := Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)
  unfold multAt
  rw [add_comm]
  exact key
end FiltrationStepLength
end GroundTheory.Heights₂.Heights.NumbersDVR
