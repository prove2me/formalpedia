-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalQuotCentred_proof_5c3e45083b88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:48:42.98396+00:00
-- url     : https://prove2.me/submissions/6c55e61f-6d59-4cd1-a37a-4894f5b5ff50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalQuotCentred
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalNormalIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalQuotCentred
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relIndex_mulLeft_eq_26923943b6c1

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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LocalQuotCentred
theorem _root_.solution (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2
end LocalQuotCentred
end GroundTheory.Heights₂.Heights
