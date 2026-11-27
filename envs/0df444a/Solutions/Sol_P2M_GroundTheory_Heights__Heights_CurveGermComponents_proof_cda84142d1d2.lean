-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveGermComponents_proof_cda84142d1d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:27.669041+00:00
-- url     : https://prove2.me/submissions/edd034c6-9726-490f-92e2-3a79957290db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_isClosed_zeroSet_c220d7e66673
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_localRingAt_eq_one_19a511e12773
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalDimDomain_proof_aafc8deef599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99


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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.CurveGermComponents
theorem _root_.solution : CurveGermComponents.Statement := by
  intro n I q hdim
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  refine ⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩
  · exact (Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW =>
      (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2
  · rintro x ⟨hxI, hxN⟩
    obtain ⟨W, hW, hxW⟩ := exists_minimalPrime_mem_zeroSet hxI
    have hqW : q ∈ zeroSet W := by
      by_contra hq
      exact Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW
    refine ⟨W, hW, ?_, hqW, hxW⟩
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_nat W
    have h1 := LocalDimDomain.proof n e W hWp he q hqW
    rw [ringKrullDim_localRingAt_eq_one hW hqW hdim] at h1
    rw [he]
    exact_mod_cast h1.symm
end GroundTheory.Heights₂.Heights.CurveGermComponents
