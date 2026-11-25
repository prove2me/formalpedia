-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:50.615858+00:00
-- url     : https://prove2.me/submissions/a733a006-cbed-44fd-b37d-a1c473f7fc35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal

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
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution :
    letI := Localization.AtPrime.algebraOfLiesOver (P.under A) P
    (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P))
        (Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P)) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
