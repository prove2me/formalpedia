-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:49.303223+00:00
-- url     : https://prove2.me/submissions/2dd4d408-a17b-4f73-9271-1a159c3ffd8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x x' : MRing ι R} (h : x - x' ∈ P) : divCycle P x = divCycle P x' := by
  have hJ : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {x'} := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.add_mem _ (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x'})
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x') : x' ∈ P ⊔ Ideal.span {x'})
      rwa [sub_add_cancel] at this
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x) : x ∈ P ⊔ Ideal.span {x})
        (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x})
      rwa [sub_sub_cancel] at this
  funext W
  unfold divCycle
  split_ifs with h1 h2 h2
  · simp only [hJ]
  · exact absurd (hJ ▸ h1) h2
  · exact absurd (hJ.symm ▸ h2) h1
  · rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
