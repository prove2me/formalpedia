-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_sum_split_24529285042b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:20.727422+00:00
-- url     : https://prove2.me/submissions/bafeb275-02a1-45bd-b23c-07f82f2b19dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution {r : ℕ} (l : Fin r) (f : Fin r → ℕ) :
    ∑ j, f j = (∑ j ∈ Finset.univ.filter (fun j => j < l), f j) + f l +
      ∑ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < l),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · rw [Finset.sum_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
