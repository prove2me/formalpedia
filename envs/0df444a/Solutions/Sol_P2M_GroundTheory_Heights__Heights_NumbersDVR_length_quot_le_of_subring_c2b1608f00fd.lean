-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quot_le_of_subring_c2b1608f00fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:29.274097+00:00
-- url     : https://prove2.me/submissions/00f6bbc7-1b1d-42af-9700-8686f125b6e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpOrderLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_subring_map_maximal_cases_ed7859abe5d9

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
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)
end GroundTheory.Heights₂.Heights.NumbersDVR
