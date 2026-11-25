-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:23:47.74159+00:00
-- url     : https://prove2.me/submissions/561d221d-887f-4bd0-a8f0-a0c0ef36f481

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac


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
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
open GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
theorem _root_.solution [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  show IsLocalization.mk' (FractionRing A) a u = 0
  rw [eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]
end GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
