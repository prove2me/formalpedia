-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_divCycle_eq_of_local_4c1557f3b5d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:32.24767+00:00
-- url     : https://prove2.me/submissions/ce450ddc-8700-4246-af38-0c6a444c9d27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution {P : Ideal (MRing κ)} {f g : MRing κ}
    (h : ∀ W : Ideal (MRing κ), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    divCycle P f = divCycle P g := by
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hf : W ∈ divSupp P f
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hf.1.1.1 (le_sup_left.trans hf.1.1.2) hf.2
    obtain ⟨hg, e⟩ := mem_divSupp_and_multAt_eq hf hu hv huv
    rw [if_pos hf, if_pos hg, e]
  · by_cases hg : W ∈ divSupp P g
    · obtain ⟨u, v, hu, hv, huv⟩ := h W hg.1.1.1 (le_sup_left.trans hg.1.1.2) hg.2
      exact absurd (mem_divSupp_and_multAt_eq hg hv hu (by rw [← neg_sub]; exact P.neg_mem huv)).1 hf
    · rw [if_neg hf, if_neg hg]
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
