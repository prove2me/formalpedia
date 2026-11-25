-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:57.264455+00:00
-- url     : https://prove2.me/submissions/ce63be53-8972-47df-8a73-be9cc81d1177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRiemannExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace RiemannExt
theorem _root_.solution {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (P : Ideal A) [P.IsPrime] (c : A) (hc : c ∉ P) :
    ∃ x : A →ₐ[ℂ] ℂ, (∀ a ∈ P, x a = 0) ∧ x c ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hJ : P.jacobson = P := IsJacobsonRing.out ‹_› (Ideal.IsPrime.isRadical ‹_›)
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf] at hc
  push Not at hc
  obtain ⟨m, ⟨hPm, hm⟩, hcm⟩ := hc
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  let e : ℂ ≃ₐ[ℂ] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun a ha => ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 (hPm ha)]
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hcm
end RiemannExt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
