-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isHomogeneous_sup_a11a066662f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:18.904645+00:00
-- url     : https://prove2.me/submissions/622cd4f3-a2cf-4bc0-ba31-1cfd70409f5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
theorem _root_.solution (T : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    (W ⊔ Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)) := by
  obtain ⟨G, hG, rfl⟩ := hW
  rw [← Ideal.span_union]
  apply Ideal.homogeneous_span
  rintro x (hx | hx)
  · obtain ⟨b, hb⟩ := hG x hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hb⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hs⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
