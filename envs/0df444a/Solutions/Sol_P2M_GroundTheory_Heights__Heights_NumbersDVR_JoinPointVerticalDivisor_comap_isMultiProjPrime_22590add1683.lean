-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_comap_isMultiProjPrime_22590add1683
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:23.546879+00:00
-- url     : https://prove2.me/submissions/1bfd9181-021e-41b1-aa74-a81c67dd91ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86


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
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
theorem _root_.solution {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (liftVar (ι := ι) ι'))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
    exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
