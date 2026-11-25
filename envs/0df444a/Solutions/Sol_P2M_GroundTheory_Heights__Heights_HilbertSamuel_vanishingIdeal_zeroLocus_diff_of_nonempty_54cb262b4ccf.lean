-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_vanishingIdeal_zeroLocus_diff_of_nonempty_54cb262b4ccf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:13.335589+00:00
-- url     : https://prove2.me/submissions/509ebdc8-4f2e-40bd-ae24-191a8f163cd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {σ : Type} [Fintype σ]
    (W J : Ideal (MvPolynomial σ ℂ)) [hW : W.IsPrime]
    (hne : (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty) :
    vanishingIdeal ℂ (zeroLocus ℂ W \ zeroLocus ℂ J) = W := by
  refine le_antisymm ?_ ?_
  · intro f hf
    obtain ⟨z₀, hz₀W, hz₀J⟩ := hne
    simp only [mem_zeroLocus_iff, not_forall] at hz₀J
    obtain ⟨g, hgJ, hg⟩ := hz₀J
    have hgW : g ∉ W := fun h => hg (hz₀W g h)
    have hfg : f * g ∈ W := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W, mem_vanishingIdeal_iff]
      intro z hz
      by_cases hzJ : z ∈ zeroLocus ℂ J
      · rw [map_mul, hzJ g hgJ, mul_zero]
      · rw [map_mul, (mem_vanishingIdeal_iff.mp hf) z ⟨hz, hzJ⟩, zero_mul]
    exact (hW.mem_or_mem hfg).resolve_right hgW
  · calc W ≤ vanishingIdeal ℂ (zeroLocus ℂ W) := le_vanishingIdeal_zeroLocus W
      _ ≤ _ := vanishingIdeal_anti_mono Set.sdiff_subset
end GroundTheory.Heights₂.Heights.HilbertSamuel
