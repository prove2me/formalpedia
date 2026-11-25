-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:26.045847+00:00
-- url     : https://prove2.me/submissions/854647e1-ee58-46c8-9f2b-c93001f7828b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {σ R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (f : R →+* S) (P : Ideal (MvPolynomial σ R))
    (hP : ∀ p ∈ P, ∀ d, homogeneousComponent d p ∈ P) :
    (P.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ S) := by
  have hspan : P.map (MvPolynomial.map f) =
      Ideal.span {x | ∃ p ∈ P, ∃ d, x = MvPolynomial.map f (homogeneousComponent d p)} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, ← sum_homogeneousComponent p, map_sum]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨p, hp, d, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨p, hp, d, rfl⟩
      exact Ideal.mem_map_of_mem _ (hP p hp d)
  rw [hspan]
  refine isHomogeneous_span_of ?_
  rintro _ ⟨p, -, d, rfl⟩
  exact ⟨d, by rw [map_homogeneousComponent]; exact homogeneousComponent_isHomogeneous _ _⟩
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
