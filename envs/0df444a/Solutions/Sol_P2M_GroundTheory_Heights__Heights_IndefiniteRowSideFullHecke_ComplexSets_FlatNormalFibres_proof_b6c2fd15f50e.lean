-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatNormalFibres_proof_b6c2fd15f50e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:34.17203+00:00
-- url     : https://prove2.me/submissions/a8b5f7c9-1575-48da-b153-44dc38e92c9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreRFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalRing_of_isIntegrallyClosed_b2b17b8cac09
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_serreAt_of_isIntegrallyClosed_3a2a85072b20

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FlatNormalFibres
theorem _root_.solution (hC : SerreCriterion.Statement) (hR : SerreRFlatAscent.Statement)
    (hS : SerreSFlatAscent.Statement) : FlatNormalFibres.Statement := by
  intro R S _ _ _ hRn hSn hloc hflat hdom hic hfib
  obtain ⟨hR1, hR2⟩ := (hC R hRn).mp (normalRing_of_isIntegrallyClosed R)
  have hfib' : ∀ (P : Ideal S) [P.IsPrime],
      SerreRAt (primeFibreLocalRing R P) 1 ∧ SerreSAt (primeFibreLocalRing R P) 2 := fun P _ => by
    obtain ⟨h1, h2⟩ := hfib P
    exact serreAt_of_isIntegrallyClosed hC _
  have hN : NormalRing S := (hC S hSn).mpr
    ⟨hR R S hRn hSn hflat 1 hR1 fun P _ => (hfib' P).1, hS R S hRn hSn hflat 2 hR2 fun P _ => (hfib' P).2⟩
  obtain ⟨hd, hi⟩ := hN (maximalIdeal S)
  exact ⟨(localizationAtMaximalEquiv S).symm.toMulEquiv.isDomain,
    IsIntegrallyClosed.of_equiv (localizationAtMaximalEquiv S)⟩
end FlatNormalFibres
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
