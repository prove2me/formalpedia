-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_isPairExpansion_08f53602d8c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:04.923095+00:00
-- url     : https://prove2.me/submissions/40dcb323-a4a5-4e99-af05-5d050cd6ed16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_expansion_f69d2f136b96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n m : ℕ} {A : MvPolynomial (Fin n) ℤ} (hA : A.IsHomogeneous m) :
    ∃ Gs, IsPairExpansion m A Gs := by
  obtain ⟨Gs, hG⟩ := exists_expansion A
  have hL : ∀ i, (X (Sum.inl i) - X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin n) ℤ).IsHomogeneous 1 :=
    fun i => (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  have hD : (rename Sum.inl A - rename Sum.inr A).IsHomogeneous m :=
    hA.rename_isHomogeneous.sub hA.rename_isHomogeneous
  have key := congrArg (homogeneousComponent m) hG
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hD), if_pos rfl, map_sum]
    at key
  simp only [homogeneousComponent_linear_mul (hL _)] at key
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, ?_, fun i => isHomogeneous_zero _ _ _⟩
    simpa using key
  · refine ⟨fun i => homogeneousComponent (m - 1) (Gs i), ?_,
      fun i => homogeneousComponent_isHomogeneous _ _⟩
    rw [key]
    simp only [hm.ne', if_false]
end GroundTheory.Heights₂.Heights.NumbersDVR
