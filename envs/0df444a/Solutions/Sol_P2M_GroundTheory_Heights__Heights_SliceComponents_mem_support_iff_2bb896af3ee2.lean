-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:25.54989+00:00
-- url     : https://prove2.me/submissions/15af0ffa-a602-4491-8cf5-7b69a4065cc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceComponents
theorem _root_.solution {J W : Ideal (MvPolynomial (Fin n) F)} {u ℓ : Fin n → F}
    (hℓ : ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) :
    W ∈ (divCycle J u).support ↔ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes ∧ linForm ℓ ∉ W := by
  refine ⟨fun h => ⟨(mem_support_divCycle.mp h).1.1, hℓ W h⟩, fun ⟨hm, hW⟩ => ?_⟩
  refine mem_support_divCycle.mpr ⟨⟨hm, ?_⟩, localMult_ne_zero hm⟩
  by_contra hr
  simp only [IsRelevant, not_exists, not_not] at hr
  exact hW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hr j))
end GroundTheory.Heights₂.Heights.SliceComponents
