-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:40.596803+00:00
-- url     : https://prove2.me/submissions/567fd67a-62bd-46b8-af01-d8e784f744ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LinearIndependentAdjoinOfTranscendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
theorem _root_.solution {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) {κ : Type*} {b : κ → A}
    (hb : LinearIndependent K b) :
    LinearIndependent (IntermediateField.adjoin K {t}) (A.val ∘ b) := by
  refine (LinearIndependent.iff_fractionRing (Algebra.adjoin K {t})
    (IntermediateField.adjoin K {t})).1 ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : ∀ j, ∃ p : K[X], aeval t p = (g j : E) := fun j => by
    have h : (g j : E) ∈ (aeval t : K[X] →ₐ[K] E).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (g j).2
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hp using hp
  have hsum : ∑ j ∈ s, aeval t (p j) * (b j : E) = 0 := by
    simpa [hp, Subalgebra.smul_def] using hg
  let P : A[X] := ∑ j ∈ s, C (b j) * (p j).map (algebraMap K A)
  have hP : aeval t P = 0 := by
    simp only [P, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hP0 : P = 0 := by
    by_contra hne
    exact ht ⟨P, hne, hP⟩
  have hcoeff : ∀ n, ∑ j ∈ s, (p j).coeff n • b j = 0 := by
    intro n
    have := congrArg (fun q => q.coeff n) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := by
    ext n
    exact linearIndependent_iff'.1 hb s (fun j => (p j).coeff n) (hcoeff n) i hi
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
