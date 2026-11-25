-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_form_a0e783e68924
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:38.564656+00:00
-- url     : https://prove2.me/submissions/6005c801-39db-4f7d-b860-66d31bab4054

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CompsDim
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  blockWeight)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P) (c : K → ℕ) :
    ∃ s : MRing ι ℂ, IsMultiHomog s c ∧ s ∉ P := by
  choose i hi using hP.relevant
  have hpr := hP.isPrime
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have h : IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, i k⟩ : MRing ι ℂ) ^ c k)
        (∑ k, c k • blockWeight ι ⟨k, i k⟩) :=
      IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℂ _ _).pow (c k)
    have hw : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hw] at h
    exact h
  · intro hm
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hi k (hpr.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
