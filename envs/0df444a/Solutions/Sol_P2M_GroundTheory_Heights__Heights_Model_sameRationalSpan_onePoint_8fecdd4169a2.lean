-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:22.223106+00:00
-- url     : https://prove2.me/submissions/207af383-913e-40f4-b5a0-fd4cf393efab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (o o' : Type) [CommRing o] [CommRing o'] [Algebra o ℚ] [Algebra o' ℚ]
    (h : ∀ a : o, ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o ℚ a = z)
    (h' : ∀ a : o', ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o' ℚ a = z) :
    SameRationalSpan ((scaledTrivBundle o onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle o' onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by
  have key : ∀ (o o' : Type) [CommRing o] [CommRing o'] [Algebra o ℚ] [Algebra o' ℚ],
      (∀ a : o, ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o ℚ a = z) →
      ∀ v ∈ (scaledTrivBundle o onePoint 1 (one_ne_zero (α := ℚ))).lat (), ∃ N : ℕ, 0 < N ∧
        N • v ∈ (scaledTrivBundle o' onePoint 1 (one_ne_zero (α := ℚ))).lat () := by
    intro o o' _ _ _ _ h v hv
    have hv' : v ∈ scaledTrivLat o onePoint 1 1 () := hv
    obtain ⟨a, ha, hva⟩ := mem_scaledTrivLat.1 hv' 0
    rw [chartRing_onePoint o] at ha
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha
    obtain ⟨N, hN, z, hz⟩ := h c
    refine ⟨N, hN, (mem_scaledTrivLat (R := o')).2 fun q => ⟨(z : ℚ), ?_, ?_⟩⟩
    · exact intCast_mem _ z
    · have hq : q = 0 := Subsingleton.elim _ _
      subst hq
      simp only [Pi.smul_apply, hva, one_mul, nsmul_eq_mul, hz]
  exact ⟨key o o' h, key o' o h'⟩
end GroundTheory.Heights₂.Heights.Model
