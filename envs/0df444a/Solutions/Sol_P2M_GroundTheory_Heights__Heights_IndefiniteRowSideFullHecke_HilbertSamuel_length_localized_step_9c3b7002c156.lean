-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:33.06384+00:00
-- url     : https://prove2.me/submissions/b9828d39-1aea-4dc4-b64f-ddc0e9050bf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution (p : Ideal R) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    (A B : Submodule R M) (x : M) (q : Ideal R) (hB : B = A ⊔ Submodule.span R {x})
    (hq : ∀ s : R, s • x ∈ A ↔ s ∈ q) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ A)) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ q)) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (M ⧸ B)) := by
  have hAB : A ≤ B := hB ▸ le_sup_left
  let f : (R ⧸ q) →ₗ[R] M ⧸ A := Submodule.liftQ q (A.mkQ ∘ₗ LinearMap.toSpanSingleton R M x) (by
    intro s hs
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (hq s).mpr hs)
  let g : M ⧸ A →ₗ[R] M ⧸ B := A.mapQ B LinearMap.id hAB
  have hf_mk : ∀ s : R, f (Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • x) := fun s => rfl
  refine length_localized_eq_add p f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
    rw [LinearMap.mem_ker, hf_mk, Submodule.Quotient.mk_eq_zero] at hy
    exact (Submodule.Quotient.mk_eq_zero q).mpr ((hq s).mp hy)
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective B y
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective A y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, hB,
      Set.mem_range]
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, z, hz, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      refine ⟨Submodule.Quotient.mk s, ?_⟩
      rw [hf_mk, Submodule.Quotient.eq]
      simpa using A.neg_mem ha
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective q y
      rw [hf_mk, Submodule.Quotient.eq] at hy
      refine ⟨m - s • x, ?_, s • x, Submodule.mem_span_singleton.mpr ⟨s, rfl⟩, sub_add_cancel _ _⟩
      simpa using A.neg_mem hy
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
