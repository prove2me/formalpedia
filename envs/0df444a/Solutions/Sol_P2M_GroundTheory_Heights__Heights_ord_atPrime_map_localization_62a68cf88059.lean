-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ord_atPrime_map_localization_62a68cf88059
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:57.584796+00:00
-- url     : https://prove2.me/submissions/a939334f-0dc3-4c7a-8dfd-5f6238552fa2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] (M : Submonoid R) (P : Ideal R)
    [hP : P.IsPrime] (hd : Disjoint (M : Set R) P) [hP' : (P.map (algebraMap R (Localization M))).IsPrime]
    (x : R) :
    Ring.ord (Localization.AtPrime (P.map (algebraMap R (Localization M))))
        (algebraMap (Localization M) _ (algebraMap R _ x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by
  have hc : (P.map (algebraMap R (Localization M))).comap (algebraMap R (Localization M)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (Localization M) hP hd
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
    (P.map (algebraMap R (Localization M)))
  rw [← IsScalarTower.algebraMap_apply, ← e.commutes x]
  exact (ord_ringEquiv e.toRingEquiv _).trans (ord_atPrime_congr hc x)
end GroundTheory.Heights₂.Heights
