-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:19.44415+00:00
-- url     : https://prove2.me/submissions/3afeb4fe-696c-4732-ba89-535f4a2d7f60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω] {τ : Type*}
variable {R}
variable (R)
variable {K : Type*} [Fintype K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (y : (Σ k, ι k) → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) :
    IsFlagFrame y (scaledTrivBundle R (segreVec y) r hs) (scaledBasis r hs) 0 where
  graded c hc i := by
    have hd : degLat R y ((0 : Fin r → K → ℤ) i) c = (chartRing R (segreVec y) c : Set Ω) := by
      ext u
      simp [degLat]
    rw [hd]
    ext z
    constructor
    · rintro ⟨v, hv, -, rfl⟩
      obtain ⟨a, ha, hva⟩ := (mem_scaledTrivLat).1 hv i
      rw [SetLike.mem_coe, scaledBasis_repr, hva, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      exact ha
    · intro hz
      refine ⟨Pi.single i (s * z), (mem_scaledTrivLat).2 fun q => ?_, fun j hij => ?_, ?_⟩
      · by_cases h : q = i
        · subst h
          exact ⟨z, hz, by simp⟩
        · exact ⟨0, zero_mem _, by simp [h]⟩
      · rw [scaledBasis_repr]
        simp [(ne_of_lt hij).symm]
      · rw [scaledBasis_repr]
        simp [← mul_assoc, inv_mul_cancel₀ hs]
end GroundTheory.Heights₂.Heights.NumbersDVR
