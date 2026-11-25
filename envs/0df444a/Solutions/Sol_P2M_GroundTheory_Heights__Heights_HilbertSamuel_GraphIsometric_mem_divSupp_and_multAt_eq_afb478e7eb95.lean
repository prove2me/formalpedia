-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mem_divSupp_and_multAt_eq_afb478e7eb95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:51.82886+00:00
-- url     : https://prove2.me/submissions/583b8dfc-0fa0-4262-9321-2b8cf68b4f1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_mul_mem_sup_span_b3608818911e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89


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
theorem _root_.solution {P W : Ideal (MRing κ)} {f g u v : MRing κ} (hf : W ∈ divSupp P f)
    (hu : u ∉ W) (hv : v ∉ W) (huv : u * f - v * g ∈ P) :
    W ∈ divSupp P g ∧ multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hvu : v * g - u * f ∈ P := by
    rw [← neg_sub]
    exact P.neg_mem huv
  have hWp : W.IsPrime := hf.1.1.1
  refine ⟨⟨GroundTheory.Heights₂.Heights.NumbersDVR.mem_minimalPrimes_of_mul_mem hu hv (mul_mem_sup_span huv)
    (mul_mem_sup_span hvu) hf.1, hf.2⟩, ?_⟩
  unfold multAt
  rw [dif_pos hWp, dif_pos hWp,
    GroundTheory.Heights₂.Heights.NumbersDVR.length_localized_eq_of_mul_mem hu hv (mul_mem_sup_span huv)
      (mul_mem_sup_span hvu)]
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
